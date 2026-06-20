#include <gtest/gtest.h>

// Annex L is exercised the way a real application selects a compatibility mode:
// the version selector is defined before the standard VPI headers are pulled
// in. 1800v2023 is chosen so that a single translation unit observes both rules
// the source listing performs for a selected version -- the chaining of the
// post-2012 selector onto 1800v2012, and the retargeting of the standard entry
// points to their version-suffixed variants. The "at most one selector" guard
// (a #error) cannot be observed by a passing test, since tripping it would stop
// this file from compiling at all; only one selector is defined here.
#define VPI_COMPATIBILITY_VERSION_1800v2023
#include "simulator/vpi_compatibility.h"

namespace {

// Expand-then-stringize so the post-preprocessor spelling of a retargeted entry
// point can be compared as text.
#define ANNEX_L_STR(x) #x
#define ANNEX_L_XSTR(x) ANNEX_L_STR(x)

// Enumerated claim 3a: including the header establishes its include guard.
TEST(VpiCompatibilityHeader, VersionMacroAvailable) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "VPI_COMPATIBILITY_H not defined after inclusion";
#endif
}

// Enumerated claim 3c: the listing chains the post-2012 selectors onto
// 1800v2012, so a 1800v2023 selection must leave 1800v2012 defined as well.
// (1800v2017 chains identically but cannot be co-selected here -- the
// at-most-one-selector rule forbids defining two selectors in one unit.)
TEST(VpiCompatibilityHeader, VersionChaining2023Implies2012) {
#if defined(VPI_COMPATIBILITY_VERSION_1800v2023) && \
    defined(VPI_COMPATIBILITY_VERSION_1800v2012)
  SUCCEED();
#else
  FAIL() << "1800v2023 should chain onto 1800v2012";
#endif
}

// Enumerated claim 3d: for the resolved version every standard entry point in
// the listing is retargeted to its version-suffixed variant. With 2023 chained
// to 2012 each public name must expand to its 1800v2012 spelling. All fourteen
// entry points are checked so the whole retarget block is observed, not a
// sample of it.
TEST(VpiCompatibilityHeader, EntryPointsRetargetedToResolvedVersion) {
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_compare_objects),
               "vpi_compare_objects_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_control), "vpi_control_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get), "vpi_get_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get_str), "vpi_get_str_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get_value), "vpi_get_value_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle), "vpi_handle_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_index),
               "vpi_handle_by_index_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_multi_index),
               "vpi_handle_by_multi_index_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_name),
               "vpi_handle_by_name_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_multi), "vpi_handle_multi_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_iterate), "vpi_iterate_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_put_value), "vpi_put_value_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_register_cb), "vpi_register_cb_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_scan), "vpi_scan_1800v2012");
}

}  // namespace
