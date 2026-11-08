#include <gtest/gtest.h>

#include <string>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "helpers_command_line.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiDefaultCompatibilityMode : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiDefaultCompatibilityMode, SettingDefaultModeMakesItCurrent) {
  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), 0);

  EXPECT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), vpiMode1364v2001);
}

TEST_F(VpiDefaultCompatibilityMode, SecondDifferentSelectionIsRefused) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  EXPECT_FALSE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), vpiMode1364v2001);
}

TEST_F(VpiDefaultCompatibilityMode, ReselectingSameModeIsAccepted) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));

  EXPECT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), vpiMode1800v2005);
}

TEST_F(VpiDefaultCompatibilityMode, SelectingNativeModeStillLocksTheRun) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(0));

  EXPECT_FALSE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), 0);
}

TEST_F(VpiDefaultCompatibilityMode,
       DefaultGovernsApplicationsNotUsingMechanism1) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2005));

  EXPECT_EQ(vpi_ctx_.EffectiveCompatibilityMode(false, 0), vpiMode1364v2005);
}

TEST_F(VpiDefaultCompatibilityMode, Mechanism1ApplicationKeepsItsOwnMode) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2005));

  EXPECT_EQ(vpi_ctx_.EffectiveCompatibilityMode(true, vpiMode1800v2009),
            vpiMode1800v2009);
}

TEST_F(VpiDefaultCompatibilityMode, TheDefaultGovernsAnApplicationsIteration) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject int_var;
  int_var.type = vpiIntVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &int_var};

  vpiHandle current = vpi_iterate(vpiVariables, VpiHandleOf(&scope));
  ASSERT_NE(current, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(current)), &reg);
  EXPECT_EQ(VpiObjectOf(vpi_scan(current)), &int_var);
  EXPECT_EQ(vpi_scan(current), nullptr);

  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  vpiHandle older = vpi_iterate(vpiVariables, VpiHandleOf(&scope));
  ASSERT_NE(older, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(older)), &int_var);
  EXPECT_EQ(vpi_scan(older), nullptr);
}

TEST_F(VpiDefaultCompatibilityMode, An1800DefaultLeavesTheBehaviorAsItIs) {
  VpiObject reg;
  reg.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg};

  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));

  vpiHandle it = vpi_iterate(vpiVariables, VpiHandleOf(&scope));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &reg);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST(VpiDefaultCompatibilityModeSwitch, TheDriverTakesEachAnnexMMode) {
  const std::pair<std::string, int> kModes[] = {
      {"1364v1995", vpiMode1364v1995},
      {"1364v2001", vpiMode1364v2001},
      {"1364v2005", vpiMode1364v2005},
      {"1800v2005", vpiMode1800v2005},
      {"1800v2009", vpiMode1800v2009}};
  for (const auto& [name, mode] : kModes) {
    CliOptions opts;
    EXPECT_TRUE(ParseCommandLine({"--vpi-compat-mode", name, "top.sv"}, opts))
        << name;
    EXPECT_EQ(opts.vpi_compat_mode, mode) << name;
  }
  CliOptions none;
  EXPECT_TRUE(ParseCommandLine({"top.sv"}, none));
  EXPECT_EQ(none.vpi_compat_mode, 0);
}

TEST(VpiDefaultCompatibilityModeSwitch, ANameWithNoModeValueIsRefused) {
  CliOptions opts;
  EXPECT_FALSE(
      ParseCommandLine({"--vpi-compat-mode", "1800v2012", "top.sv"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_EQ(opts.vpi_compat_mode, 0);
  CliOptions bare;
  EXPECT_FALSE(ParseCommandLine({"top.sv", "--vpi-compat-mode"}, bare));
  EXPECT_TRUE(bare.rejected_argument);
}

TEST(VpiDefaultCompatibilityModeSwitch, OnlyOneDefaultModeIsSelectable) {
  CliOptions twice;
  EXPECT_FALSE(ParseCommandLine({"--vpi-compat-mode", "1364v1995",
                                 "--vpi-compat-mode", "1800v2009", "top.sv"},
                                twice));
  EXPECT_TRUE(twice.rejected_argument);
  EXPECT_EQ(twice.vpi_compat_mode, vpiMode1364v1995);
  CliOptions same;
  EXPECT_TRUE(ParseCommandLine({"--vpi-compat-mode", "1364v2005",
                                "--vpi-compat-mode", "1364v2005", "top.sv"},
                               same));
  EXPECT_EQ(same.vpi_compat_mode, vpiMode1364v2005);
}

}  // namespace
}  // namespace delta
