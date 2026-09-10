#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace {

// §36.11 (List of VPI routines by functional category) divides the VPI routines
// into nine groups "based on primary functionality" and names every routine of
// each in Table 36-1 through Table 36-9. What the clause asks of a tool is that
// it provide them: the categories are of routines an application calls, and a
// routine the tool does not supply is a category it does not answer for.
//
// Taking a routine's address odr-uses it, so a non-null pointer for each is the
// trace that the simulator supplies the interface and that it resolves at link
// time. The nine groups are checked one case apiece, in the clause's own order.

// Table 36-1: simulation-related callbacks.
TEST(VpiRoutineCategories, SimulationRelatedCallbacksAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_cb), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_remove_cb), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_cb_info), nullptr);
}

// Table 36-2: system task and system function callbacks.
TEST(VpiRoutineCategories, SystemTaskAndFunctionCallbacksAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_systf), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_systf_info), nullptr);
}

// Table 36-3: traversing the SystemVerilog hierarchy. The clause pairs
// vpi_iterate() with vpi_scan() for the one-to-many relationships, so the two
// are provided together or the category answers for neither.
TEST(VpiRoutineCategories, HierarchyTraversalRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_iterate), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_scan), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_multi), nullptr);
}

// Table 36-4: accessing properties of objects.
TEST(VpiRoutineCategories, PropertyAccessRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get64), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_str), nullptr);
}

// Table 36-5: accessing objects from properties.
TEST(VpiRoutineCategories, ObjectFromPropertyRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_name), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_index), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_multi_index), nullptr);
}

// Table 36-6: delay processing. Table 36-7: logic and strength value
// processing. Table 36-8: simulation time processing.
TEST(VpiRoutineCategories, DelayValueAndTimeRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_delays), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_delays), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_time), nullptr);
}

// Table 36-9: miscellaneous utilities - the writing and flushing routines.
TEST(VpiRoutineCategories, MiscellaneousOutputRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_printf), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_vprintf), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_flush), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_mcd_open), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_mcd_close), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_mcd_printf), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_mcd_vprintf), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_mcd_flush), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_mcd_name), nullptr);
}

// Table 36-9 continued: the utilities that are not about output.
TEST(VpiRoutineCategories, MiscellaneousUtilityRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_vlog_info), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_compare_objects), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_chk_error), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_data), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_data), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_userdata), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_userdata), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_release_handle), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_control), nullptr);
}

// The categories are of routines an application calls, so each is provided with
// the interface its own subclause of Clause 38 gives it. A type or index
// argument is the PLI_INT32 those Arguments rows name, and a status result is
// PLI_INT32 - not the plain int several of the traversal and utility routines
// were declared with, which said nothing about which of the two it meant. The
// routines Clause 38 defines beyond these tables carry the same types, since
// the header spells one interface.
static_assert(
    std::is_same_v<decltype(vpi_handle), vpiHandle(PLI_INT32, vpiHandle)>,
    "§38.18: vpi_handle takes a PLI_INT32 type");
static_assert(
    std::is_same_v<decltype(vpi_iterate), vpiHandle(PLI_INT32, vpiHandle)>,
    "§38.23: vpi_iterate takes a PLI_INT32 type");
static_assert(std::is_same_v<decltype(vpi_handle_multi),
                             vpiHandle(PLI_INT32, vpiHandle, vpiHandle)>,
              "§38.22: vpi_handle_multi takes a PLI_INT32 type");
static_assert(std::is_same_v<decltype(vpi_handle_by_index),
                             vpiHandle(vpiHandle, PLI_INT32)>,
              "§38.19: vpi_handle_by_index takes a PLI_INT32 index");
static_assert(
    std::is_same_v<decltype(vpi_handle_by_multi_index),
                   vpiHandle(vpiHandle, PLI_INT32, PLI_INT32*)>,
    "§38.20: vpi_handle_by_multi_index takes a PLI_INT32 count and array");
static_assert(std::is_same_v<decltype(vpi_compare_objects),
                             PLI_INT32(vpiHandle, vpiHandle)>,
              "§38.6: vpi_compare_objects answers with a PLI_INT32");
static_assert(std::is_same_v<decltype(vpi_remove_cb), PLI_INT32(vpiHandle)>,
              "§38.39: vpi_remove_cb answers with a PLI_INT32");

}  // namespace
