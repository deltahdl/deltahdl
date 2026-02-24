// §annex_l.2

#include <gtest/gtest.h>
#include "vpi/vpi_compatibility.h"

namespace {

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

}  // namespace
