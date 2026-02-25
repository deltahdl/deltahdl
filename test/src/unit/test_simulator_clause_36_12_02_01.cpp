// §36.12.2.1: Mechanism 1: Compile-based binding to a compatibility mode

#include <gtest/gtest.h>

#include "vpi/vpi_compatibility.h"

namespace {

TEST(VpiCompatL2, DefaultNoRemapping) {
#ifndef VPI_COMPATIBILITY_VERSION_1364v1995
#ifndef VPI_COMPATIBILITY_VERSION_1364v2001
#ifndef VPI_COMPATIBILITY_VERSION_1800v2005
  SUCCEED();
#endif
#endif
#endif
}

}  // namespace
