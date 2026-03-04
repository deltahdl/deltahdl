#include <gtest/gtest.h>

#include "simulator/vpi_compatibility.h"

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
