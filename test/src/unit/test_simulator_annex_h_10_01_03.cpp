#include <gtest/gtest.h>

#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, HandleTypes) {
  svScope scope = nullptr;
  svOpenArrayHandle arr = nullptr;
  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(arr, nullptr);
}

// H.10.1.3 declares svScope (a scope instance) and svOpenArrayHandle (a generic
// object) as opaque handles. Beyond holding null, each must be able to carry an
// arbitrary object address and yield it back unchanged, since callers round-trip
// real pointers through these handle types.
TEST(SvDpi, HandleTypesCarryOpaquePointers) {
  int scope_object = 0;
  int array_object = 0;
  svScope scope = &scope_object;
  svOpenArrayHandle arr = &array_object;
  EXPECT_EQ(scope, static_cast<void*>(&scope_object));
  EXPECT_EQ(arr, static_cast<void*>(&array_object));
  EXPECT_NE(scope, arr);
}

// H.10.1.3: a tool using the VPI-based canonical value representation reports
// the version string "1800-2005". This simulator uses s_vpi_vecval as its
// canonical value, so svDpiVersion() shall return exactly that string.
TEST(SvDpi, DpiVersionReportsVpiCanonicalRepresentation) {
  const char* ver = svDpiVersion();
  ASSERT_NE(ver, nullptr);
  EXPECT_STREQ(ver, "1800-2005");
}

}
