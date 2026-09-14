#include <gtest/gtest.h>

// §L.2 is the source code of vpi_compatibility.h, and these tests read
// src/simulator/vpi_compatibility.h the way the listing is written to be read:
// with one VPI_COMPATIBILITY_VERSION_ symbol defined as 1 ahead of it, the
// value §36.12.2.1 has the application give the symbol it selects and the
// value a -D on the compiler command line gives. The file is read directly
// here rather than through vpi_user.h because the listing is what is under
// observation; test_simulator_annex_l_01.cpp reads it the way §L.1 has
// application code reach it.
//
// Two of the listing's rules halt compilation and so cannot be observed by a
// passing test. The file opens by testing for its own mark and raising an
// error if it finds it, so a second reading in one translation unit is
// rejected rather than ignored; and each version's branch raises an error if
// any other version is selected beside it. What can be observed is the mark
// the first reading leaves, which is why every section below undefines it
// before reading the file again: the file has no include guard to reset, only
// the mark of a reading it refuses to repeat.
#define VPI_COMPATIBILITY_VERSION_1800v2023 1
#include "simulator/vpi_compatibility.h"

namespace {

// Expand-then-stringize so the post-preprocessor spelling of a retargeted entry
// point can be compared as text.
#define ANNEX_L_STR(x) #x
#define ANNEX_L_XSTR(x) ANNEX_L_STR(x)

// §L.2: the file defines VPI_COMPATIBILITY_H as the mark of its first reading,
// the mark its opening #error looks for.
TEST(VpiCompatibilityHeader, VersionMacroAvailable) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "VPI_COMPATIBILITY_H not defined after inclusion";
#endif
}

// §L.2: the listing chains 1800v2023 onto 1800v2012 by defining the 1800v2012
// symbol, and then selects the branch to take by testing the symbols' values
// with #if and #elif rather than by whether they are defined. So the chained
// symbol has to carry a value that #if reads as true, which this test reads
// the same way the listing does -- a symbol defined with no value would not
// preprocess here at all.
TEST(VpiCompatibilityHeader, VersionChaining2023Implies2012) {
#if VPI_COMPATIBILITY_VERSION_1800v2012
  SUCCEED();
#else
  FAIL() << "1800v2023 should chain onto 1800v2012";
#endif
}

// §L.2: for the version resolved, every one of the fourteen entry points the
// listing names is redefined to its version-suffixed variant. With 2023
// chained to 2012 each public name expands to its 1800v2012 spelling. All
// fourteen are read so the whole branch is observed, not a sample of it.
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

// §L.2: the other chaining rule, 1800v2017 onto 1800v2012, written the same
// way. Selecting 1800v2017 beside 1800v2023 would show nothing: both chain
// onto 1800v2012, whose branch finds no other version selected and raises no
// error for the pair, so this section reads the file again with only
// 1800v2017 defined.
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

// §L.2: the branches are selected by value. The listing writes #if and #elif
// over the version symbols, so a symbol defined as 0 selects nothing: none of
// the fourteen entry points is renamed, and no chained symbol appears. A file
// that selected by definition alone, with #ifdef, would rename them all here.
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

// §L.2: a version the listing gives its own branch is taken by that branch
// and chains onto nothing -- 1364v2005 renames the fourteen entry points to
// their 1364v2005 variants and leaves the 1800v2012 symbol undefined.
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
