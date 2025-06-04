#!/bin/bash
set -e

# Commit/tag of STP to build – keep in sync with upstream stable release
STP_VERSION=1bdfe50

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p "$DEPS"

# Detect number of cores for parallel build
if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi

if [ ! -d "$DEPS/stp" ]; then
    echo "Cloning STP (version $STP_VERSION) …"
    cd "$DEPS"
    git clone https://github.com/stp/stp.git
    chmod -R 777 stp
    cd stp
    git checkout -f "$STP_VERSION"

    echo "Initializing and updating submodules..."
    git submodule init && git submodule update

    # STP provides helper scripts for building its dependencies. At the moment we
    # only need minisat, which is mandatory. The script below will clone and
    # install minisat into stp/deps/install.
    ./scripts/deps/setup-minisat.sh
    ./scripts/deps/setup-outputcheck.sh
    ./scripts/deps/setup-cms.sh

    # Location where the helper script installed the libraries
    STP_DEPS_PREFIX="$(pwd)/deps/install"

    # Copy missing libraries to install location
    cp "deps/cadical/build/libcadical.so" "$STP_DEPS_PREFIX/lib/" 2>/dev/null || true
    cp "deps/cadiback/libcadiback.so" "$STP_DEPS_PREFIX/lib/" 2>/dev/null || true

    echo "Configuring STP …"
    mkdir -p build
    cd build
    cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_PREFIX_PATH="$STP_DEPS_PREFIX" \
        -DCMAKE_INSTALL_PREFIX="$DEPS/install" \
        -DENABLE_TESTING=OFF \
        -DENABLE_PYTHON_INTERFACE=OFF \
        -DGTEST_CREATE_SHARED_LIBRARY=OFF \
        -DGTEST_HAS_PTHREAD=OFF \
        -DFETCHCONTENT_QUIET=OFF \
        -DFETCHCONTENT_FULLY_DISCONNECTED=ON

    echo "Compiling STP (using $NUM_CORES cores) …"
    make -j"$NUM_CORES"
    cd "$DIR"
else
    echo "$DEPS/stp already exists. If you want to rebuild, please remove it manually."
fi

# Sanity-check that the static library was produced
if [ -f "$DEPS/stp/build/lib/libstp.a" ] || [ -f "$DEPS/stp/build/lib/libstp.so" ]; then
    echo "It appears stp was setup successfully into $DEPS/stp."
    echo "You may now install it with ./configure.sh --stp && cd build && make"
    echo ""
    echo "To run tests, export the library path:"
    echo "export LD_LIBRARY_PATH=\"$DEPS/stp/deps/install/lib:\$LD_LIBRARY_PATH\""
else
    echo "Building stp failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/stp/stp"
    exit 1
fi 