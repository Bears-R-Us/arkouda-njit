#!/bin/bash

module load intel
module load imkl

ROOT_DIR=$PWD
export LD_LIBRARY_PATH=$ROOT_DIR/arachne/server/external_libs/install/lib64:$LD_LIBRARY_PATH
export LIBRARY_PATH=$ROOT_DIR/arachne/server/external_libs/install/lib64:$LIBRARY_PATH
export CPATH=$ROOT_DIR/arachne/server/external_libs/install/include:$CPATH

echo "Cloning submodules..."
git submodule update --init --recursive

echo "Building igraph..."
cd arachne/server/external_libs/igraph
mkdir -p build
cd build
cmake .. -DCMAKE_INSTALL_PREFIX=../../install -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DBUILD_SHARED_LIBS=ON
cmake --build . --target install
cd ../../../../../

pwd

echo "Building libleidenalg..."
cd arachne/server/external_libs/libleidenalg
mkdir -p build
cd build
cmake .. -DCMAKE_PREFIX_PATH=../../install -DCMAKE_INSTALL_PREFIX=../../install
cmake --build . --target install
cd ../../../../../

cd arachne/server/leiden_helpers/
g++ -O3 -w -fPIC \
    -I$ROOT_DIR/arachne/server/external_libs/install/include \
    -c computeLeiden.cpp -o computeLeiden.o
cd ../../../

