// §L.2: vpi_compatibility.h source code

#include <gtest/gtest.h>

#include "vpi/vpi_compatibility.h"

namespace {

TEST(VpiCompatL2, HeaderIncludable) {
  // Simply including the header should compile.
  SUCCEED();
}

TEST(VpiCompatL2, VersionMacroAvailable) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "VPI_COMPATIBILITY_H not defined after inclusion";
#endif
}

TEST(VpiCompatL2, VersionChaining2023Implies2012) {
#ifdef VPI_COMPATIBILITY_VERSION_1800v2023
#ifdef VPI_COMPATIBILITY_VERSION_1800v2012
  SUCCEED();
#else
  FAIL() << "1800v2023 should imply 1800v2012";
#endif
#else
  SUCCEED();
#endif
}

TEST(VpiCompatL2, DefaultNoRemapping) {
#ifndef VPI_COMPATIBILITY_VERSION_1364v1995
#ifndef VPI_COMPATIBILITY_VERSION_1364v2001
#ifndef VPI_COMPATIBILITY_VERSION_1800v2005
  SUCCEED();
#endif
#endif
#endif
}

} // namespace
