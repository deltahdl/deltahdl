#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_globals.h"

namespace {

#ifdef VPI_USER_H
constexpr bool kSvFileBroughtTheBaseFile = true;
#else
constexpr bool kSvFileBroughtTheBaseFile = false;
#endif

}  // namespace

#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace {

#ifdef VPI_USER_H
constexpr bool kGuardHeldAcrossTheRepeat = true;
#else
constexpr bool kGuardHeldAcrossTheRepeat = false;
#endif

}  // namespace

namespace delta {
namespace {

TEST(PliIncludeFiles, TheSvFileBringsTheBaseFileWithIt) {
  EXPECT_TRUE(kSvFileBroughtTheBaseFile);
  EXPECT_TRUE(kGuardHeldAcrossTheRepeat);
}

TEST(PliIncludeFiles, TheBaseFileDefinesTheConstantsReservedToIt) {
  EXPECT_GE(vpiModule, 1);
  EXPECT_LE(vpiModule, 299);
  EXPECT_GE(vpiIntVal, 1);
  EXPECT_LE(vpiIntVal, 299);
  EXPECT_GE(cbValueChange, 1);
  EXPECT_LE(cbValueChange, 299);
}

TEST(PliIncludeFiles, TheSvFileDefinesTheConstantsReservedToIt) {
  EXPECT_GE(vpiPackage, 600);
  EXPECT_LE(vpiPackage, 999);
  EXPECT_GE(vpiInterface, 600);
  EXPECT_LE(vpiInterface, 999);
  EXPECT_GE(vpiClassVar, 600);
  EXPECT_LE(vpiClassVar, 999);
}

TEST(PliIncludeFiles, TheFilesDefineTheStructuresTheRoutinesAreCalledWith) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 7;
  EXPECT_EQ(value.format, vpiIntVal);
  EXPECT_EQ(value.value.integer, 7);

  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 5;
  EXPECT_EQ(time.type, vpiSimTime);
  EXPECT_EQ(time.low, 5u);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  EXPECT_EQ(cb.reason, cbValueChange);

  s_vpi_assertion_step_info step = {};
  step.stateFrom = 1;
  step.stateTo = 2;
  EXPECT_EQ(step.stateFrom, 1);
  EXPECT_EQ(step.stateTo, 2);
}

class PliIncludeFileLibrary : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(PliIncludeFileLibrary, AnApplicationIncludingTheFilesReachesTheLibrary) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");

  vpiHandle systf = vpi_register_systf(&data);
  ASSERT_NE(systf, nullptr);

  s_vpi_systf_data read_back = {};
  vpi_get_systf_info(systf, &read_back);
  EXPECT_EQ(read_back.type, vpiSysTask);
  ASSERT_NE(read_back.tfname, nullptr);
  EXPECT_STREQ(read_back.tfname, "$probe");
}

}  // namespace
}  // namespace delta
