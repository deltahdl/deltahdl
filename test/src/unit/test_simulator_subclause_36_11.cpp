#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/vpi_user.h"

namespace {

TEST(VpiRoutineCategories, SimulationRelatedCallbacksAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_cb), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_remove_cb), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_cb_info), nullptr);
}

TEST(VpiRoutineCategories, SystemTaskAndFunctionCallbacksAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_systf), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_systf_info), nullptr);
}

TEST(VpiRoutineCategories, HierarchyTraversalRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_iterate), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_scan), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_multi), nullptr);
}

TEST(VpiRoutineCategories, PropertyAccessRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get64), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_str), nullptr);
}

TEST(VpiRoutineCategories, ObjectFromPropertyRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_name), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_index), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_multi_index), nullptr);
}

TEST(VpiRoutineCategories, DelayValueAndTimeRoutinesAreProvided) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_delays), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_delays), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_time), nullptr);
}

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

static_assert(
    std::is_same_v<decltype(vpi_handle), vpiHandle(PLI_INT32, vpiHandle)>,
    "§38.18: vpi_handle takes a PLI_INT32 type");
static_assert(
    std::is_same_v<decltype(vpi_iterate), vpiHandle(PLI_INT32, vpiHandle)>,
    "§38.23: vpi_iterate takes a PLI_INT32 type");
static_assert(std::is_same_v<decltype(vpi_handle_multi),
                             vpiHandle(PLI_INT32, vpiHandle, vpiHandle, ...)>,
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
