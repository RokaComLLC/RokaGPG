#!/bin/bash
 
# 
# This script was inspired by http://blog.diogot.com/blog/2013/09/18/static-libs-with-support-to-ios-5-and-arm64/
#
# This script uses a temporary folder for intermediate build products.
#
# Minimum deployment target is 5.0 for 32 bit architectures and for 64 bit architectures it is 7.0.
#
 
if [ -z "$1" ]; then
  echo
  echo "usage: $0 <project.xcodeproj> [<target>]"
  echo
  echo "for example: $0 ~/Documents/MyStaticLibProject.xcodeproj"
  echo
  echo "will generate a fat library (i386, x86_64, armv7, armv7s and arm64) named libMyStaticLibProject.a in the current folder for the target MyStaticLibProject."
  echo
  exit
fi
 
if [ ! -d "$1" ]; then
  echo
  echo "Error: $1 does not exist"
  echo
  exit
fi
 
MY_PROJECT="$1"
MY_PROJECT_NAME=$(basename "$1")
 
if [ -z "$2" ]; then
	MY_TARGET=${MY_PROJECT_NAME%.*}
else
	MY_TARGET="$2"
fi
 
MY_STATIC_LIB="lib${MY_TARGET}.a"
MY_BUILD_PATH=`mktemp -d -t "build"`
 
# armv7, armv7s
MY_ARM_BUILD_PATH="${MY_BUILD_PATH}/build-arm"
MY_CURRENT_BUILD_PATH="${MY_ARM_BUILD_PATH}"
xcodebuild -project "${MY_PROJECT}" -target "${MY_TARGET}" -configuration 'Release' -sdk 'iphoneos7.1' clean build ARCHS='armv7 armv7s' VALID_ARCHS='armv7 armv7s' IPHONEOS_DEPLOYMENT_TARGET='5.0' TARGET_BUILD_DIR="${MY_CURRENT_BUILD_PATH}" BUILT_PRODUCTS_DIR="${MY_CURRENT_BUILD_PATH}" OBJROOT="${MY_CURRENT_BUILD_PATH}" SYMROOT="${MY_CURRENT_BUILD_PATH}"
 
# arm64
MY_ARM64_BUILD_PATH="${MY_BUILD_PATH}/build-arm64"
MY_CURRENT_BUILD_PATH="${MY_ARM64_BUILD_PATH}"
xcodebuild -project "${MY_PROJECT}" -target "${MY_TARGET}" -configuration 'Release' -sdk 'iphoneos7.1' clean build ARCHS='arm64' VALID_ARCHS='arm64' IPHONEOS_DEPLOYMENT_TARGET='7.0' TARGET_BUILD_DIR="${MY_CURRENT_BUILD_PATH}" BUILT_PRODUCTS_DIR="${MY_CURRENT_BUILD_PATH}" OBJROOT="${MY_CURRENT_BUILD_PATH}" SYMROOT="${MY_CURRENT_BUILD_PATH}"
 
# i386
MY_I386_BUILD_PATH="${MY_BUILD_PATH}/build-i386"
MY_CURRENT_BUILD_PATH="${MY_I386_BUILD_PATH}"
xcodebuild -project "${MY_PROJECT}" -target "${MY_TARGET}" -configuration 'Release' -sdk 'iphonesimulator7.1' clean build ARCHS='i386' VALID_ARCHS='i386' IPHONEOS_DEPLOYMENT_TARGET='5.0' TARGET_BUILD_DIR="${MY_CURRENT_BUILD_PATH}" BUILT_PRODUCTS_DIR="${MY_CURRENT_BUILD_PATH}" OBJROOT="${MY_CURRENT_BUILD_PATH}" SYMROOT="${MY_CURRENT_BUILD_PATH}"
 
# x86_64
MY_X86_64_BUILD_PATH="${MY_BUILD_PATH}/build-x86_64"
MY_CURRENT_BUILD_PATH="${MY_X86_64_BUILD_PATH}"
xcodebuild -project "${MY_PROJECT}" -target "${MY_TARGET}" -configuration 'Release' -sdk 'iphonesimulator7.1' clean build ARCHS='x86_64' VALID_ARCHS='x86_64' IPHONEOS_DEPLOYMENT_TARGET='7.0' TARGET_BUILD_DIR="${MY_CURRENT_BUILD_PATH}" BUILT_PRODUCTS_DIR="${MY_CURRENT_BUILD_PATH}" OBJROOT="${MY_CURRENT_BUILD_PATH}" SYMROOT="${MY_CURRENT_BUILD_PATH}"
 
lipo -create "${MY_ARM_BUILD_PATH}/${MY_STATIC_LIB}" "${MY_ARM64_BUILD_PATH}/${MY_STATIC_LIB}" "${MY_I386_BUILD_PATH}/${MY_STATIC_LIB}" "${MY_X86_64_BUILD_PATH}/${MY_STATIC_LIB}" -output "${MY_STATIC_LIB}"

OUTDIR=./build 
mkdir -p ${OUTDIR} 
mv ${MY_STATIC_LIB} ${OUTDIR}
rm -rf "${MY_BUILD_PATH}"
