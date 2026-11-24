#include <gtest/gtest.h>

#define VPI_COMPATIBILITY_VERSION_1800v2023 1
#include "simulator/vpi_compatibility.h"

namespace {

#define ANNEX_L_STR(x) #x
#define ANNEX_L_XSTR(x) ANNEX_L_STR(x)

TEST(VpiCompatibilityHeader, VersionMacroAvailable) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "VPI_COMPATIBILITY_H not defined after inclusion";
#endif
}

TEST(VpiCompatibilityHeader, VersionChaining2023Implies2012) {
#if VPI_COMPATIBILITY_VERSION_1800v2012
  SUCCEED();
#else
  FAIL() << "1800v2023 should chain onto 1800v2012";
#endif
}

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

#undef vpi_compare_objects
#undef vpi_control
#undef vpi_get
#undef vpi_get_str
#undef vpi_get_value
#undef vpi_handle
#undef vpi_handle_by_index
#undef vpi_handle_by_multi_index
#undef vpi_handle_by_name
#undef vpi_handle_multi
#undef vpi_iterate
#undef vpi_put_value
#undef vpi_register_cb
#undef vpi_scan
#undef VPI_COMPATIBILITY_VERSION_1364v1995
#undef VPI_COMPATIBILITY_VERSION_1364v2001
#undef VPI_COMPATIBILITY_VERSION_1364v2005
#undef VPI_COMPATIBILITY_VERSION_1800v2005
#undef VPI_COMPATIBILITY_VERSION_1800v2009
#undef VPI_COMPATIBILITY_VERSION_1800v2012
#undef VPI_COMPATIBILITY_VERSION_1800v2017
#undef VPI_COMPATIBILITY_VERSION_1800v2023
#undef VPI_COMPATIBILITY_H

#define VPI_COMPATIBILITY_VERSION_1800v2017 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityHeader, VersionChaining2017Implies2012) {
#if VPI_COMPATIBILITY_VERSION_1800v2012
  SUCCEED();
#else
  FAIL() << "1800v2017 should chain onto 1800v2012";
#endif
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get), "vpi_get_1800v2012");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_scan), "vpi_scan_1800v2012");
}

}  // namespace

#undef vpi_compare_objects
#undef vpi_control
#undef vpi_get
#undef vpi_get_str
#undef vpi_get_value
#undef vpi_handle
#undef vpi_handle_by_index
#undef vpi_handle_by_multi_index
#undef vpi_handle_by_name
#undef vpi_handle_multi
#undef vpi_iterate
#undef vpi_put_value
#undef vpi_register_cb
#undef vpi_scan
#undef VPI_COMPATIBILITY_VERSION_1364v1995
#undef VPI_COMPATIBILITY_VERSION_1364v2001
#undef VPI_COMPATIBILITY_VERSION_1364v2005
#undef VPI_COMPATIBILITY_VERSION_1800v2005
#undef VPI_COMPATIBILITY_VERSION_1800v2009
#undef VPI_COMPATIBILITY_VERSION_1800v2012
#undef VPI_COMPATIBILITY_VERSION_1800v2017
#undef VPI_COMPATIBILITY_VERSION_1800v2023
#undef VPI_COMPATIBILITY_H

#define VPI_COMPATIBILITY_VERSION_1364v2001 0
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityHeader, AVersionSymbolDefinedAsZeroSelectsNothing) {
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_compare_objects), "vpi_compare_objects");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_control), "vpi_control");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get), "vpi_get");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get_str), "vpi_get_str");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get_value), "vpi_get_value");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle), "vpi_handle");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_index), "vpi_handle_by_index");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_multi_index),
               "vpi_handle_by_multi_index");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_name), "vpi_handle_by_name");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_multi), "vpi_handle_multi");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_iterate), "vpi_iterate");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_put_value), "vpi_put_value");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_register_cb), "vpi_register_cb");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_scan), "vpi_scan");
#if VPI_COMPATIBILITY_VERSION_1800v2012
  FAIL() << "no version was selected, so nothing should chain onto 1800v2012";
#else
  SUCCEED();
#endif
}

}  // namespace

#undef vpi_compare_objects
#undef vpi_control
#undef vpi_get
#undef vpi_get_str
#undef vpi_get_value
#undef vpi_handle
#undef vpi_handle_by_index
#undef vpi_handle_by_multi_index
#undef vpi_handle_by_name
#undef vpi_handle_multi
#undef vpi_iterate
#undef vpi_put_value
#undef vpi_register_cb
#undef vpi_scan
#undef VPI_COMPATIBILITY_VERSION_1364v1995
#undef VPI_COMPATIBILITY_VERSION_1364v2001
#undef VPI_COMPATIBILITY_VERSION_1364v2005
#undef VPI_COMPATIBILITY_VERSION_1800v2005
#undef VPI_COMPATIBILITY_VERSION_1800v2009
#undef VPI_COMPATIBILITY_VERSION_1800v2012
#undef VPI_COMPATIBILITY_VERSION_1800v2017
#undef VPI_COMPATIBILITY_VERSION_1800v2023
#undef VPI_COMPATIBILITY_H

#define VPI_COMPATIBILITY_VERSION_1364v2005 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityHeader, AVersionWithItsOwnBranchChainsOntoNothing) {
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_compare_objects),
               "vpi_compare_objects_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_control), "vpi_control_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get), "vpi_get_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get_str), "vpi_get_str_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_get_value), "vpi_get_value_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle), "vpi_handle_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_index),
               "vpi_handle_by_index_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_multi_index),
               "vpi_handle_by_multi_index_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_by_name),
               "vpi_handle_by_name_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_handle_multi), "vpi_handle_multi_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_iterate), "vpi_iterate_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_put_value), "vpi_put_value_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_register_cb), "vpi_register_cb_1364v2005");
  EXPECT_STREQ(ANNEX_L_XSTR(vpi_scan), "vpi_scan_1364v2005");
#ifdef VPI_COMPATIBILITY_VERSION_1800v2012
  FAIL() << "1364v2005 should chain onto nothing";
#else
  SUCCEED();
#endif
}

}  // namespace
