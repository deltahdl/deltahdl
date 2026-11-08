#include <gtest/gtest.h>

#define DELTA_VPI_STR2(x) #x
#define DELTA_VPI_STR(x) DELTA_VPI_STR2(x)

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
#include "simulator/vpi_user.h"

namespace {

TEST(VpiCompatibilityModeBinding, VpiUserHeaderPerformsTheRedefinition) {
  EXPECT_STREQ(DELTA_VPI_STR(vpi_compare_objects),
               "vpi_compare_objects_1364v2005");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_get), "vpi_get_1364v2005");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_handle), "vpi_handle_1364v2005");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_iterate), "vpi_iterate_1364v2005");
  EXPECT_STREQ(DELTA_VPI_STR(vpi_scan), "vpi_scan_1364v2005");
}

}  // namespace
