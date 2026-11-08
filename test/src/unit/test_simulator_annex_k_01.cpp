#include <gtest/gtest.h>

#include <string_view>
#include <type_traits>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_include_file.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(VpiUserHeaderProvided, TheAnnexShowsANormativeFileEverySimulatorProvides) {
  EXPECT_EQ(VpiAnnexShowingVpiUserH(), "Annex K");
  EXPECT_EQ(VpiUserHFileName(), "vpi_user.h");
  EXPECT_TRUE(VpiUserHIsNormative());
  EXPECT_TRUE(VpiUserHIsProvidedByEverySimulator());
}

TEST(VpiUserHeaderProvided, TheFileTheAnnexNamesIsTheOneProvided) {
#ifdef VPI_USER_H
  SUCCEED();
#else
  FAIL() << "vpi_user.h, the file Annex K shows, is not provided";
#endif
}

static_assert(std::is_same_v<decltype(vpi_register_cb), vpiHandle(s_cb_data*)>,
              "vpi_user.h must provide vpi_register_cb");
static_assert(
    std::is_same_v<decltype(vpi_get), PLI_INT32(PLI_INT32, vpiHandle)>,
    "vpi_user.h must provide vpi_get");
static_assert(
    std::is_same_v<decltype(vpi_get_str), PLI_BYTE8*(PLI_INT32, vpiHandle)>,
    "vpi_user.h must provide vpi_get_str");
static_assert(std::is_same_v<decltype(vpi_iterate), vpiHandle(int, vpiHandle)>,
              "vpi_user.h must provide vpi_iterate");
static_assert(std::is_same_v<decltype(vpi_scan), vpiHandle(vpiHandle)>,
              "vpi_user.h must provide vpi_scan");
static_assert(
    std::is_same_v<decltype(vpi_get_value), void(vpiHandle, s_vpi_value*)>,
    "vpi_user.h must provide vpi_get_value");
static_assert(std::is_same_v<decltype(vpi_handle_by_name),
                             vpiHandle(PLI_BYTE8*, vpiHandle)>,
              "vpi_user.h must provide vpi_handle_by_name");

TEST(VpiUserHeaderProvided, IncludeFileIsPresentAndGuarded) {
#ifdef SV_VPI_USER_H
  SUCCEED();
#else
  FAIL() << "vpi_user.h include guard not provided by the simulator";
#endif
}

TEST(VpiUserHeaderProvided, ProvidesCanonicalVpiTypes) {
  EXPECT_TRUE(std::is_pointer_v<vpiHandle>);

  s_vpi_value value = {};
  s_vpi_time time = {};
  s_cb_data cb = {};
  vpiHandle handle = nullptr;
  EXPECT_EQ(value.format, 0);
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(cb.reason, 0);
  EXPECT_EQ(handle, nullptr);
}

TEST(VpiUserHeaderProvided, ProvidesResolvableAccessRoutines) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_cb), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_iterate), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_scan), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_name), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_printf), nullptr);
}

TEST(VpiUserHeaderProvided, IdempotentUnderRepeatedInclusion) {
#ifdef SV_VPI_USER_H
  s_vpi_value value = {};
  value.format = 0;
  EXPECT_EQ(value.format, 0);
#else
  FAIL() << "vpi_user.h guard not latched after repeated inclusion";
#endif
}

}  // namespace
