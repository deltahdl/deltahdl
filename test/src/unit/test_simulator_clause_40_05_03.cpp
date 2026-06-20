#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/coverage_control.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

// Clause 40.5.3 extends vpi_control() so a PLI client can control the
// collection of coverage. The control constant selects the action:
// vpiCoverageStart/Stop/Reset/Check carry the semantics of $coverage_control()
// (§40.3.2.1) and act on the instance or assertion a handle names;
// vpiCoverageSave carries the semantics of $coverage_save() (§40.3.2.5) and
// vpiCoverageMerge the semantics of $coverage_merge() (§40.3.2.4), both against
// a named coverage database. The status the equivalent system function returns
// is reported back, so each test observes both the status and the
// collection-state change the production routine applies.

namespace delta {
namespace {

class VpiCoverageControlSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  static int Status(CoverageStatus s) { return static_cast<int>(s); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// C1/C2: vpi_control(vpiCoverageStart, <coverageType>, instance_handle) starts
// the collection of coverage over the instance the handle names, applying the
// §40.3.2.1 Start rule: collection begins, and the operation reports `SV_COV_OK
// when the whole scope is coverable. The no-effect rule of a repeated start is
// applied too - a second start still succeeds but does not begin collection
// afresh.
TEST_F(VpiCoverageControlSim, StartControlsCoverageOverTheInstanceHandle) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");

  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut"));
  int result = vpi_control(vpiCoverageStart, vpiAssertCoverage, dut);
  EXPECT_EQ(result, Status(CoverageStatus::kOk));
  EXPECT_TRUE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut"));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().StartCount("top.dut"), 1u);

  // A redundant start has no effect: it still succeeds, but collection does not
  // start a second time.
  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().StartCount("top.dut"), 1u);
}

// C1: the third argument of vpi_control() may be an assertion handle as well as
// an instance handle. Control through an assertion handle acts on that
// assertion's own scope, independently of an enclosing instance: assertion
// coverage is not confined to instance-level control the way statement, toggle,
// and FSM coverage are (§40.5.3). The same control rules are applied, just to
// the scope the assertion handle names.
TEST_F(VpiCoverageControlSim, ControlAcceptsAnAssertionHandle) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", CoverageAvailability::kFull);
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut.a1", CoverageAvailability::kFull);
  VpiHandle assertion = vpi_ctx_.CreateAssertion("top.dut.a1", vpiAssertion);

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, assertion),
            Status(CoverageStatus::kOk));
  EXPECT_TRUE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut.a1"));
  // Controlling the assertion did not implicitly start its enclosing instance;
  // the action was scoped to the assertion the handle names.
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut"));
}

// C2: vpiCoverageStop stops collection and vpiCoverageReset clears collected
// coverage, both per §40.3.2.1 - the same control rules the $coverage_control()
// system function applies, reached now through vpi_control().
TEST_F(VpiCoverageControlSim, StopAndResetApplyTheControlRules) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");
  ASSERT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));

  EXPECT_EQ(vpi_control(vpiCoverageStop, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut"));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().StopCount("top.dut"), 1u);

  EXPECT_EQ(vpi_control(vpiCoverageReset, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().ResetCount("top.dut"), 1u);
}

// C2: vpiCoverageCheck reports whether coverage can be obtained without
// changing the collection state, per §40.3.2.1. A fully coverable scope reports
// `SV_COV_OK and a scope offering no coverage of the type reports
// `SV_COV_NOCOV; neither query starts collection.
TEST_F(VpiCoverageControlSim, CheckReportsAvailabilityWithoutChangingState) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.full", CoverageAvailability::kFull);
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.none", CoverageAvailability::kNone);
  VpiHandle full = vpi_ctx_.CreateModule("full", "top.full");
  VpiHandle none = vpi_ctx_.CreateModule("none", "top.none");

  EXPECT_EQ(vpi_control(vpiCoverageCheck, vpiStatementCoverage, full),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_control(vpiCoverageCheck, vpiStatementCoverage, none),
            Status(CoverageStatus::kNoCoverage));
  // Checking is a pure query: it does not begin collection.
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.full"));
}

// C1/C2: a control request whose handle names a scope the design does not
// contain is a bad argument; the §40.3.2.1 rules report `SV_COV_ERROR. A null
// handle likewise names no scope and is an error.
TEST_F(VpiCoverageControlSim, ControlOnUnknownScopeIsAnError) {
  VpiHandle ghost = vpi_ctx_.CreateModule("ghost", "top.ghost");
  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, ghost),
            Status(CoverageStatus::kError));
  EXPECT_EQ(
      vpi_control(vpiCoverageStart, vpiAssertCoverage, VpiHandle{nullptr}),
      Status(CoverageStatus::kError));
}

// C3: statement, toggle, and FSM coverage are controllable only at the instance
// level, not on a per-statement, per-signal, or per-FSM basis. Control applies
// to the instance the handle names as a whole: starting with one coverage type
// and stopping with a different type over the same instance handle act on one
// shared instance-level collection state.
TEST_F(VpiCoverageControlSim, CoverageIsControllableOnlyAtInstanceLevel) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");

  // Start statement coverage on the instance.
  ASSERT_EQ(vpi_control(vpiCoverageStart, vpiStatementCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_TRUE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut"));

  // Stopping toggle coverage over the same instance handle stops the very same
  // instance-level collection - the control is not bound to an individual
  // statement, signal, or FSM.
  EXPECT_EQ(vpi_control(vpiCoverageStop, vpiToggleCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut"));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().StopCount("top.dut"), 1u);
}

// C4: vpi_control(vpiCoverageSave, <coverageType>, name) saves the current
// coverage of the type to the named database, per $coverage_save() (§40.3.2.5):
// `SV_COV_OK and a recorded save when the type is available, `SV_COV_NOCOV and
// nothing saved when it is not.
TEST_F(VpiCoverageControlSim, SaveAppliesCoverageSaveRules) {
  vpi_ctx_.GetCoverageControlState().SetCoverageAvailableForSave(
      vpiAssertCoverage, true);

  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiAssertCoverage, "covdb"),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().SaveCount("covdb"), 1u);

  // A type with no coverage available to save records nothing.
  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiToggleCoverage, "toggledb"),
            Status(CoverageStatus::kNoCoverage));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().SaveCount("toggledb"), 0u);
}

// C5: vpi_control(vpiCoverageMerge, <coverageType>, name) merges coverage of
// the type from the named database into the simulation, per $coverage_merge()
// (§40.3.2.4): `SV_COV_OK and a recorded merge when the database belongs to
// this design and holds the type, `SV_COV_ERROR when the name does not exist.
TEST_F(VpiCoverageControlSim, MergeAppliesCoverageMergeRules) {
  vpi_ctx_.GetCoverageControlState().RegisterCoverageDatabase(
      "covdb", /*from_this_design=*/true, {vpiAssertCoverage});

  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "covdb"),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().MergeCount("covdb"), 1u);

  // A name no database is recorded under cannot be loaded: an error, with no
  // merge performed.
  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "missing"),
            Status(CoverageStatus::kError));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().MergeCount("missing"), 0u);
}

}  // namespace
}  // namespace delta
