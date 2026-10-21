#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/coverage_control.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// §40.5.3 extends vpi_control() so a PLI client can control the
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

  // §40.3.1 coverage-type constants. The coverage state is keyed by these, and
  // §40.5.1's properties name the same types to vpi_control(), so a case that
  // primes the state names the type here and asks for it there.
  static constexpr int kSvCovAssertion = 20;
  static constexpr int kSvCovStatement = 22;
  static constexpr int kSvCovToggle = 23;

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
      "top.dut", kSvCovAssertion, CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");

  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting(
      "top.dut", kSvCovAssertion));
  int result = vpi_control(vpiCoverageStart, vpiAssertCoverage, dut);
  EXPECT_EQ(result, Status(CoverageStatus::kOk));
  EXPECT_TRUE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut",
                                                              kSvCovAssertion));
  EXPECT_EQ(
      vpi_ctx_.GetCoverageControlState().StartCount("top.dut", kSvCovAssertion),
      1u);

  // A redundant start has no effect: it still succeeds, but collection does not
  // start a second time.
  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(
      vpi_ctx_.GetCoverageControlState().StartCount("top.dut", kSvCovAssertion),
      1u);
}

// C2: vpiCoverageStop stops collection and vpiCoverageReset clears collected
// coverage, both per §40.3.2.1 - the same control rules the $coverage_control()
// system function applies, reached now through vpi_control().
TEST_F(VpiCoverageControlSim, StopAndResetApplyTheControlRules) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", kSvCovAssertion, CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");
  ASSERT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));

  EXPECT_EQ(vpi_control(vpiCoverageStop, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting(
      "top.dut", kSvCovAssertion));
  EXPECT_EQ(
      vpi_ctx_.GetCoverageControlState().StopCount("top.dut", kSvCovAssertion),
      1u);

  EXPECT_EQ(vpi_control(vpiCoverageReset, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(
      vpi_ctx_.GetCoverageControlState().ResetCount("top.dut", kSvCovAssertion),
      1u);
}

// C2: vpiCoverageCheck reports whether coverage can be obtained without
// changing the collection state, per §40.3.2.1. A fully coverable scope reports
// `SV_COV_OK and a scope offering no coverage of the type reports
// `SV_COV_NOCOV; neither query starts collection.
TEST_F(VpiCoverageControlSim, CheckReportsAvailabilityWithoutChangingState) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.full", kSvCovStatement, CoverageAvailability::kFull);
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.none", kSvCovStatement, CoverageAvailability::kNone);
  VpiHandle full = vpi_ctx_.CreateModule("full", "top.full");
  VpiHandle none = vpi_ctx_.CreateModule("none", "top.none");

  EXPECT_EQ(vpi_control(vpiCoverageCheck, vpiStatementCoverage, full),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_control(vpiCoverageCheck, vpiStatementCoverage, none),
            Status(CoverageStatus::kNoCoverage));
  // Checking is a pure query: it does not begin collection.
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting(
      "top.full", kSvCovStatement));
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
// level, not on a per-statement, per-signal, or per-FSM basis, and with the
// semantics of $coverage_control(), whose control acts on the coverage type
// the call names. Control applies to the instance the handle names as a whole,
// one coverage type at a time: stopping toggle coverage over the instance
// leaves the statement coverage started there collecting (#7525).
TEST_F(VpiCoverageControlSim, InstanceLevelControlActsOnTheNamedTypeAlone) {
  CoverageControlState& cov = vpi_ctx_.GetCoverageControlState();
  cov.SetAvailability("top.dut", kSvCovStatement, CoverageAvailability::kFull);
  cov.SetAvailability("top.dut", kSvCovToggle, CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");

  ASSERT_EQ(vpi_control(vpiCoverageStart, vpiStatementCoverage, dut),
            Status(CoverageStatus::kOk));
  ASSERT_EQ(vpi_control(vpiCoverageStart, vpiToggleCoverage, dut),
            Status(CoverageStatus::kOk));

  EXPECT_EQ(vpi_control(vpiCoverageStop, vpiToggleCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_FALSE(cov.IsCollecting("top.dut", kSvCovToggle));
  EXPECT_TRUE(cov.IsCollecting("top.dut", kSvCovStatement));
  EXPECT_EQ(cov.StopCount("top.dut", kSvCovStatement), 0u);
  // Nor was any other type started there.
  EXPECT_FALSE(cov.IsCollecting("top.dut", kSvCovAssertion));
}

// C3 read the way the sentence is written: the control takes an instance handle
// or an assertion handle, and statement, toggle and FSM coverage are controlled
// for a whole instance, never for one statement, one signal or one FSM. A
// signal handle is that per-signal basis, so it is a bad argument rather than a
// scope of its own. The scope it would have named is one a coverage engine
// really does keep - toggle coverage is kept per signal - so taken off the
// handle's name alone the request started collection on that one signal and
// reported `SV_COV_OK for it.
TEST_F(VpiCoverageControlSim, ASignalHandleIsNotAScopeCoverageIsControlledAt) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut.sig", kSvCovToggle, CoverageAvailability::kFull);
  VpiHandle sig = vpi_ctx_.CreateNetObj("top.dut.sig", nullptr, 8);

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiToggleCoverage, sig),
            Status(CoverageStatus::kError));
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting("top.dut.sig",
                                                               kSvCovToggle));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().StartCount("top.dut.sig",
                                                          kSvCovToggle),
            0u);

  // Nor the reset that handle would have applied to that one signal.
  EXPECT_EQ(vpi_control(vpiCoverageReset, vpiToggleCoverage, sig),
            Status(CoverageStatus::kError));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().ResetCount("top.dut.sig",
                                                          kSvCovToggle),
            0u);
}

// C4: vpi_control(vpiCoverageSave, <coverageType>, name) saves the current
// coverage of the type to the named database, per $coverage_save() (§40.3.2.5):
// `SV_COV_OK and a recorded save when the type is available, `SV_COV_NOCOV and
// nothing saved when it is not.
TEST_F(VpiCoverageControlSim, SaveAppliesCoverageSaveRules) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", kSvCovAssertion, CoverageAvailability::kFull);

  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiAssertCoverage, "covdb"),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().SaveCount("covdb"), 1u);

  // A type with no coverage available to save records nothing: only the
  // assertion type above is available, and vpiToggleCoverage names another.
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
      "covdb", /*from_this_design=*/true, {kSvCovAssertion});

  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "covdb"),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().MergeCount("covdb"), 1u);

  // A name no database is recorded under cannot be loaded: an error, with no
  // merge performed.
  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "missing"),
            Status(CoverageStatus::kError));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().MergeCount("missing"), 0u);
}

// The status the control applied from inside the run below answered.
int g_stop_status = 0;

// The assertion of `top` named `name`, null for none.
vpiHandle TopAssertion(std::string_view name) {
  vpiHandle it =
      vpi_iterate(vpiAssertion, vpi_handle_by_name(VpiText("top"), nullptr));
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    const char* own = vpi_get_str(vpiName, obj);
    if (own != nullptr && name == own) return obj;
  }
  return nullptr;
}

// What the design's $stop_first runs: a stop of the assertion coverage of
// `first` alone, through its handle.
PLI_INT32 StopFirstCalltf(PLI_BYTE8* /*user_data*/) {
  g_stop_status =
      vpi_control(vpiCoverageStop, vpiAssertCoverage, TopAssertion("first"));
  return 0;
}

using AssertionControlRun = VpiDesignRun;

// C1: §40.5.3 controls assertion coverage one assertion at a time through its
// handle. Stopped before either succeeds, `first` gathers no coverage while
// `second`, in the same instance, still does, so the instance counts one
// covered assertion; a check through the handle answers what the instance
// offers, and a type controlled per instance alone is a bad argument on an
// assertion handle (#7540).
TEST_F(AssertionControlRun, AnAssertionHandleControlsThatAssertionAlone) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$stop_first");
  data.calltf = &StopFirstCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  first: assert property (@(posedge clk) a);\n"
      "  second: assert property (@(posedge clk) a);\n"
      "  initial begin\n"
      "    $stop_first;\n"
      "    #1 clk = 1; #1 clk = 0;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle first = TopAssertion("first");
  vpiHandle second = TopAssertion("second");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);

  EXPECT_EQ(g_stop_status, static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(vpi_get(vpiCovered, first), 0);
  EXPECT_EQ(vpi_get(vpiCovered, second), 1);
  EXPECT_EQ(
      vpi_get(vpiAssertCoverage, vpi_handle_by_name(VpiText("top"), nullptr)),
      1);
  EXPECT_EQ(vpi_control(vpiCoverageCheck, vpiAssertCoverage, first),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiStatementCoverage, first),
            static_cast<int>(CoverageStatus::kError));
}

}  // namespace
}  // namespace delta
