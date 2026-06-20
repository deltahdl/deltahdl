#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

// Clause 36.12.2.2 -- Mechanism 2: selection of the default VPI compatibility
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

}  // namespace
}  // namespace delta
