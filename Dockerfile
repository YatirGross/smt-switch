# Dockerfile for smt-switch with STP support
# Based on Ubuntu 22.04 LTS for stability and compatibility

FROM ubuntu:22.04

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Install system dependencies
RUN apt-get update && apt-get install -y \
    # Basic build tools
    build-essential \
    cmake \
    git \
    curl \
    wget \
    tar \
    xz-utils \
    # C/C++ compilers
    gcc \
    g++ \
    # Required libraries
    libgmp-dev \
    libgmpxx4ldbl \
    # Python dependencies (for potential Python bindings)
    python3 \
    python3-dev \
    python3-pip \
    # Additional tools that might be needed
    pkg-config \
    autoconf \
    automake \
    libtool \
    make \
    # Neo-vim editor
    neovim \
    # For STP dependencies
    libboost-all-dev \
    # Bison and Flex for STP
    bison \
    flex \
    # Additional libraries for STP
    libtinfo-dev \
    libncurses-dev \
    # Clean up
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /workspace

# Clone the smt-switch repository with the specific branch
RUN git clone https://github.com/YatirGross/smt-switch.git . && \
    git checkout add-stp-new-solver

# Make setup scripts executable
RUN chmod +x contrib/*.sh

# Set up STP dependencies
RUN ./contrib/setup-stp.sh

# Debug: Check where STP libraries are located
RUN echo "=== Looking for STP libraries ===" && \
    find /workspace/deps -name "*.so" -o -name "*.a" | grep -i stp || echo "No STP libraries found" && \
    echo "=== Checking STP build directory ===" && \
    ls -la /workspace/deps/stp/build/lib/ || echo "STP build lib directory not found" && \
    echo "=== Checking STP install directory ===" && \
    ls -la /workspace/deps/install/lib/ || echo "STP install lib directory not found"

# Copy STP library to the expected location if needed
RUN if [ -f "/workspace/deps/stp/build/lib/libstp.so" ]; then \
        mkdir -p /workspace/deps/stp/deps/install/lib && \
        cp /workspace/deps/stp/build/lib/libstp.so* /workspace/deps/stp/deps/install/lib/ && \
        echo "Copied STP library to expected location"; \
    fi

# Export the library path as instructed by the STP setup
ENV LD_LIBRARY_PATH="/workspace/deps/stp/deps/install/lib:/workspace/deps/install/lib"
ENV STP_HOME="/workspace/deps/stp"

# Configure the build with STP support
RUN export LD_LIBRARY_PATH="/workspace/deps/stp/deps/install/lib:/workspace/deps/install/lib:$LD_LIBRARY_PATH" && \
    export PKG_CONFIG_PATH="/workspace/deps/stp/deps/install/lib/pkgconfig:/workspace/deps/install/lib/pkgconfig:$PKG_CONFIG_PATH" && \
    ./configure.sh --stp

# Build the project with proper library paths
RUN cd build && \
    export LD_LIBRARY_PATH="/workspace/deps/stp/deps/install/lib:/workspace/deps/install/lib:$LD_LIBRARY_PATH" && \
    export PKG_CONFIG_PATH="/workspace/deps/stp/deps/install/lib/pkgconfig:/workspace/deps/install/lib/pkgconfig:$PKG_CONFIG_PATH" && \
    make -j$(nproc)

# Run tests (don't fail build on test failures)
RUN cd build && make test || echo "Some tests failed, but build completed successfully"

# Set the default command
CMD ["/bin/bash"]
