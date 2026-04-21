#!/bin/bash

# Inspired by build process of spead2

set -e -u

dnf install -y boost-devel cln-devel gmp-devel glpk-devel hwloc-devel z3-devel xerces-c-devel eigen3-devel python3-devel # missing ginac

cd /tmp

# Install ginac
ginac_version=1.8.10
curl -fsSLO https://www.ginac.de/ginac-${ginac_version}.tar.bz2
tar -jxf ginac-${ginac_version}.tar.bz2
cd ginac-${ginac_version}
./configure CXXFLAGS="-O2"
make -j ${NR_JOBS}
make install
cd ..

# Install Boost 1.83 headers (no full build)
#
# Building all Boost libraries from source is extremely slow on GitHub-hosted Linux runners
# and is unnecessary for our use (we only need Boost headers at >= 1.83 for compilation).
BOOST_VERSION=1.83.0
BOOST_VERSION_UNDERSCORE=${BOOST_VERSION//./_}
BOOST_PREFIX=/opt/boost_${BOOST_VERSION_UNDERSCORE}
curl -fsSLO https://archives.boost.io/release/${BOOST_VERSION}/source/boost_${BOOST_VERSION_UNDERSCORE}.tar.gz
tar -xzf boost_${BOOST_VERSION_UNDERSCORE}.tar.gz
mkdir -p "${BOOST_PREFIX}/include"
cp -a "boost_${BOOST_VERSION_UNDERSCORE}/boost" "${BOOST_PREFIX}/include/"

# Install Storm
: "${STORM_VERSION:=master}"
git clone --depth 1 https://github.com/moves-rwth/storm.git -b "${STORM_VERSION}"
cd storm
mkdir build
cd build
cmake .. -DSTORM_BUILD_TESTS=OFF -DSTORM_BUILD_EXECUTABLES=OFF -DSTORM_PORTABLE=ON
make -j ${NR_JOBS}
make install
cd ..
rm -rf build