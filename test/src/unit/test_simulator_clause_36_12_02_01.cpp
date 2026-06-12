#include <gtest/gtest.h>

// Clause 36.12.2.1 -- Mechanism 1: compile-based binding to a compatibility
// mode. These tests observe the production header
// (src/simulator/vpi_compatibility.h) applying the mechanism: selecting a
// single compatibility version retargets the standard VPI entry points to that
// mode's variants, and leaving every version unselected performs no remapping.
//
// Each entry point is a function name that the header redefines (as an
// object-like macro) when a mode is active. The two-step stringizer below reads
// the post-preprocessing spelling of such a name so a test can assert which
// variant it currently resolves to. Because the macro state of a translation
// unit is global, the header's include guard is reset between sections so the
// same source file can exercise several modes in textual order.

#define DELTA_VPI_STR2(x) #x
#define DELTA_VPI_STR(x) DELTA_VPI_STR2(x)

// Clears any previously selected version and remapping so the next inclusion of
// the header starts from a clean slate.
//
//   undo the 14 retargeted entry points, every selectable version symbol
//   (including the chained 1800v2012), and the include guard.

// --- Section: no version selected (default, native data model) ---
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, DefaultLeavesEntryPointsUnmapped) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_compare_objects), "vpi_compare_objects");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_control), "vpi_control");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get), "vpi_get");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get_str), "vpi_get_str");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get_value), "vpi_get_value");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_by_index), "vpi_handle_by_index");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_by_multi_index),
               "vpi_handle_by_multi_index");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_by_name), "vpi_handle_by_name");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_multi), "vpi_handle_multi");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_put_value), "vpi_put_value");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_register_cb), "vpi_register_cb");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_scan), "vpi_scan");
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

// --- Section: 1364v2001 selected (matches the standard's own example) ---
// Selecting exactly one version is admitted by the at-most-one guard and must
// redefine all fourteen entry points to that version's variant.
#define VPI_COMPATIBILITY_VERSION_1364v2001 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, SelectedVersionRetargetsEveryEntryPoint) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_compare_objects),
               "vpi_compare_objects_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_control), "vpi_control_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get), "vpi_get_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get_str), "vpi_get_str_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get_value), "vpi_get_value_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_by_index),
               "vpi_handle_by_index_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_by_multi_index),
               "vpi_handle_by_multi_index_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_by_name),
               "vpi_handle_by_name_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle_multi), "vpi_handle_multi_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_put_value), "vpi_put_value_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_register_cb), "vpi_register_cb_1364v2001");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_scan), "vpi_scan_1364v2001");
}

// Selecting one version must keep the selection singular: the header may not
// leave a second version symbol defined behind the application's back, which is
// the at-most-one invariant the compile-time guard exists to protect. (The
// guard's rejection of an explicit double selection halts compilation and so
// cannot be observed by a passing test.) 1364v2001 carries no internal version
// chaining, so none of the other seven symbols may be set here.
TEST(VpiCompatibilityModeBinding, SingleSelectionStaysSingular) {
#if defined(VPI_COMPATIBILITY_VERSION_1364v1995) || \
    defined(VPI_COMPATIBILITY_VERSION_1364v2005) || \
    defined(VPI_COMPATIBILITY_VERSION_1800v2005) || \
    defined(VPI_COMPATIBILITY_VERSION_1800v2009) || \
    defined(VPI_COMPATIBILITY_VERSION_1800v2012) || \
    defined(VPI_COMPATIBILITY_VERSION_1800v2017) || \
    defined(VPI_COMPATIBILITY_VERSION_1800v2023)
  FAIL() << "selecting 1364v2001 must not define any sibling version symbol";
#else
  SUCCEED();
#endif
}

// The redefinition mechanism is scoped to exactly the enumerated entry points.
// A standard VPI routine that is not on that list (e.g. vpi_chk_error,
// vpi_free_object) must be left untouched even while a mode is active, so an
// application's calls to it are not silently retargeted. With 1364v2001
// selected, these names must still spell themselves.
TEST(VpiCompatibilityModeBinding, SelectionDoesNotRetargetUnlistedRoutines) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_chk_error), "vpi_chk_error");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_free_object), "vpi_free_object");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get_time), "vpi_get_time");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_printf), "vpi_printf");
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

// --- Section: each remaining selectable version, one at a time ---
// Re-including the header under a different single selection exercises the rule
// for the other listed symbols; vpi_handle stands in for the whole entry-point
// set verified above. Versions that the header carries a direct variant for are
// pinned to that variant; 1800v2017 and 1800v2023 share the 1800v2012 data
// model (their variant naming is defined in Annex L), so they are only required
// to perform some redefinition away from the native name.

#define VPI_COMPATIBILITY_VERSION_1364v1995 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, Version1364v1995Retargets) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1364v1995");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1364v1995");
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

TEST(VpiCompatibilityModeBinding, Version1364v2005Retargets) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1364v2005");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1364v2005");
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

#define VPI_COMPATIBILITY_VERSION_1800v2005 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, Version1800v2005Retargets) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1800v2005");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1800v2005");
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

#define VPI_COMPATIBILITY_VERSION_1800v2009 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, Version1800v2009Retargets) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1800v2009");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1800v2009");
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

#define VPI_COMPATIBILITY_VERSION_1800v2012 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, Version1800v2012Retargets) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1800v2012");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1800v2012");
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

TEST(VpiCompatibilityModeBinding, Version1800v2017Retargets) {
  EXPECT_STRNE(DELTA_VPI_STR(vpi_handle), "vpi_handle");
  EXPECT_STRNE(DELTA_VPI_STR(vpi_iterate), "vpi_iterate");
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

#define VPI_COMPATIBILITY_VERSION_1800v2023 1
#include "simulator/vpi_compatibility.h"

namespace {

TEST(VpiCompatibilityModeBinding, Version1800v2023Retargets) {
  EXPECT_STRNE(DELTA_VPI_STR(vpi_handle), "vpi_handle");
  EXPECT_STRNE(DELTA_VPI_STR(vpi_iterate), "vpi_iterate");
}

}  // namespace
