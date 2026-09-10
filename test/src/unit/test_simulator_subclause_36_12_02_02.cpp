#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

// §36.12.2.2 -- Mechanism 2: selection of the default VPI compatibility
// mode run by the host simulator. These tests observe the simulator runtime
// (src/simulator/vpi.cpp) applying the mechanism: the simulation provider makes
// a means available to set a single run-wide default compatibility mode, that
// default governs every application not using the compile-based scheme of
// Mechanism 1, only one default is selectable for a given simulation run, and
// an application needing a different mode obtains it through Mechanism 1
// instead.

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

// §36.12.2.2: a means to set the default VPI compatibility mode shall be made
// available by the simulation provider. Before any selection the default is the
// native current-standard behavior (mode 0); selecting a mode puts it in force
// and the selection succeeds.
TEST_F(VpiDefaultCompatibilityMode, SettingDefaultModeMakesItCurrent) {
  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), 0);

  EXPECT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), vpiMode1364v2001);
}

// §36.12.2.2: only one such default mode shall be selectable for a given
// simulation run. Once a mode is selected, a request for a different mode is
// refused and the originally selected mode stays in force.
TEST_F(VpiDefaultCompatibilityMode, SecondDifferentSelectionIsRefused) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  EXPECT_FALSE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), vpiMode1364v2001);
}

// §36.12.2.2: re-selecting the mode already in force is consistent with the
// single-default rule and is accepted, leaving that mode current.
TEST_F(VpiDefaultCompatibilityMode, ReselectingSameModeIsAccepted) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));

  EXPECT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), vpiMode1800v2005);
}

// §36.12.2.2: only one default mode is selectable per run, and selecting the
// native mode (no compatibility mode) is itself that one selection. Edge case:
// choosing the native default first still fixes the run, so a later request for
// a non-native mode is refused - the selected flag, not the mode value, is what
// closes the run to further selection.
TEST_F(VpiDefaultCompatibilityMode, SelectingNativeModeStillLocksTheRun) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(0));

  EXPECT_FALSE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  EXPECT_EQ(vpi_ctx_.DefaultCompatibilityMode(), 0);
}

// §36.12.2.2: the default shall determine the compatibility-mode behavior for
// all applications not using the compile-based scheme (Mechanism 1). Such an
// application is governed by the run-wide default.
TEST_F(VpiDefaultCompatibilityMode,
       DefaultGovernsApplicationsNotUsingMechanism1) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2005));

  EXPECT_EQ(vpi_ctx_.EffectiveCompatibilityMode(/*uses_mechanism1=*/false,
                                                /*mechanism1_mode=*/0),
            vpiMode1364v2005);
}

// §36.12.2.2: an application requiring a different mode in the same run uses
// the compile-based mechanism to do so. Such an application carries its own
// mode in its recompiled entry points, so the run-wide default does not apply
// to it.
TEST_F(VpiDefaultCompatibilityMode, Mechanism1ApplicationKeepsItsOwnMode) {
  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2005));

  EXPECT_EQ(
      vpi_ctx_.EffectiveCompatibilityMode(/*uses_mechanism1=*/true,
                                          /*mechanism1_mode=*/vpiMode1800v2009),
      vpiMode1800v2009);
}

// -----------------------------------------------------------------------------
// What the default determines. §36.12.2.2 does not stop at a means to set the
// mode: it says the selection "shall determine the compatibility mode VPI
// behavior for all applications not using the compile-based scheme detailed in
// Mechanism 1". The mode was recorded, EffectiveCompatibilityMode answered
// which one governed an application, and no routine asked either - so a run
// given a default behaved exactly as a run without one and the mechanism
// determined nothing.
// -----------------------------------------------------------------------------

// §36.12.2.2 with §36.12.1 Table 36-10 row 5: an application that made no
// compile-time selection is governed by the run's default, so under an IEEE
// 1364 default its vpiVariables iteration excludes the vpiReg and vpiRegArray
// objects that standard excluded from it.
TEST_F(VpiDefaultCompatibilityMode, TheDefaultGovernsAnApplicationsIteration) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject int_var;
  int_var.type = vpiIntVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &int_var};

  // With no default selected the run behaves as this standard describes.
  vpiHandle current = vpi_iterate(vpiVariables, &scope);
  ASSERT_NE(current, nullptr);
  EXPECT_EQ(vpi_scan(current), &reg);
  EXPECT_EQ(vpi_scan(current), &int_var);
  EXPECT_EQ(vpi_scan(current), nullptr);

  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  vpiHandle older = vpi_iterate(vpiVariables, &scope);
  ASSERT_NE(older, nullptr);
  EXPECT_EQ(vpi_scan(older), &int_var);
  EXPECT_EQ(vpi_scan(older), nullptr);
}

// §36.12.2.2: a default naming one of the IEEE 1800 standards leaves the
// behavior this standard describes in place, the rows of Table 36-10 those
// versions share with it being the ones an application would notice.
TEST_F(VpiDefaultCompatibilityMode, An1800DefaultLeavesTheBehaviorAsItIs) {
  VpiObject reg;
  reg.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg};

  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));

  vpiHandle it = vpi_iterate(vpiVariables, &scope);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &reg);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

}  // namespace
}  // namespace delta
