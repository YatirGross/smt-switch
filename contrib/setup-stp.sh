#!/bin/bash
set -e

# Commit/tag of STP to build – keep in sync with upstream stable release
STP_VERSION=2.3.3

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

    echo "Building STP dependencies (minisat) …"
    # STP provides helper scripts for building its dependencies. At the moment we
    # only need minisat, which is mandatory. The script below will clone and
    # install minisat into stp/deps/install.
    ./scripts/deps/setup-minisat.sh
    ./scripts/deps/setup-cadical.sh
    ./scripts/deps/setup-gtest.sh
    ./scripts/deps/setup-outputcheck.sh
    ./scripts/deps/setup-cms.sh

    # Location where the helper script installed the libraries
    STP_DEPS_PREFIX="$(pwd)/deps/install"

    echo "Configuring STP …"
    mkdir -p build
    cd build
    cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_PREFIX_PATH="$STP_DEPS_PREFIX" \
        -DCMAKE_INSTALL_PREFIX="$DEPS/install" \
        -DENABLE_TESTING=OFF

    echo "Compiling STP (using $NUM_CORES cores) …"
    make -j"$NUM_CORES"
    cd "$DIR"
else
    echo "$DEPS/stp already exists. If you want to rebuild, please remove it manually."
fi

# Sanity-check that the static library was produced
if [ -f "$DEPS/stp/build/lib/libstp.a" ]; then
    echo "STP appears to have been built successfully in $DEPS/stp."
    echo "You may now install it with: ./configure.sh --stp && cd build && make"
else
    echo "Building STP failed (libstp.a not found)."
    echo "Please ensure all build dependencies (cmake, flex, bison, boost, gmp, etc.) are present."
    exit 1
fi 