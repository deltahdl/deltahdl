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

namespace delta {
namespace {

class VpiCoverageControlSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  static int Status(CoverageStatus s) { return static_cast<int>(s); }

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

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, dut),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(
      vpi_ctx_.GetCoverageControlState().StartCount("top.dut", kSvCovAssertion),
      1u);
}

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
  EXPECT_FALSE(vpi_ctx_.GetCoverageControlState().IsCollecting(
      "top.full", kSvCovStatement));
}

TEST_F(VpiCoverageControlSim, ControlOnUnknownScopeIsAnError) {
  VpiHandle ghost = vpi_ctx_.CreateModule("ghost", "top.ghost");
  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, ghost),
            Status(CoverageStatus::kError));
  EXPECT_EQ(
      vpi_control(vpiCoverageStart, vpiAssertCoverage, VpiHandle{nullptr}),
      Status(CoverageStatus::kError));
}

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
  EXPECT_FALSE(cov.IsCollecting("top.dut", kSvCovAssertion));
}

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

  EXPECT_EQ(vpi_control(vpiCoverageReset, vpiToggleCoverage, sig),
            Status(CoverageStatus::kError));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().ResetCount("top.dut.sig",
                                                          kSvCovToggle),
            0u);
}

TEST_F(VpiCoverageControlSim, SaveAppliesCoverageSaveRules) {
  vpi_ctx_.GetCoverageControlState().SetAvailability(
      "top.dut", kSvCovAssertion, CoverageAvailability::kFull);

  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiAssertCoverage, "covdb"),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().SaveCount("covdb"), 1u);

  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiToggleCoverage, "toggledb"),
            Status(CoverageStatus::kNoCoverage));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().SaveCount("toggledb"), 0u);
}

TEST_F(VpiCoverageControlSim, MergeAppliesCoverageMergeRules) {
  vpi_ctx_.GetCoverageControlState().RegisterCoverageDatabase(
      "covdb", true, {kSvCovAssertion});

  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "covdb"),
            Status(CoverageStatus::kOk));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().MergeCount("covdb"), 1u);

  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "missing"),
            Status(CoverageStatus::kError));
  EXPECT_EQ(vpi_ctx_.GetCoverageControlState().MergeCount("missing"), 0u);
}

int g_stop_status = 0;

vpiHandle TopAssertion(std::string_view name) {
  vpiHandle it =
      vpi_iterate(vpiAssertion, vpi_handle_by_name(VpiText("top"), nullptr));
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    const char* own = vpi_get_str(vpiName, obj);
    if (own != nullptr && name == own) return obj;
  }
  return nullptr;
}

PLI_INT32 StopFirstCalltf(PLI_BYTE8*) {
  g_stop_status =
      vpi_control(vpiCoverageStop, vpiAssertCoverage, TopAssertion("first"));
  return 0;
}

bool RegisterStopFirst() {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$stop_first");
  data.calltf = &StopFirstCalltf;
  return vpi_register_systf(&data) != nullptr;
}

using AssertionControlRun = VpiDesignRun;

TEST_F(AssertionControlRun, AnAssertionHandleControlsThatAssertionAlone) {
  ASSERT_TRUE(RegisterStopFirst());
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

  EXPECT_EQ(vpi_control(vpiCoverageReset, vpiAssertCoverage, first),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(vpi_control(vpiCoverageReset, vpiAssertCoverage, second),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(vpi_get(vpiCovered, second), 0);
  EXPECT_EQ(vpi_get(vpiAssertSuccessCovered, second), 0);
  EXPECT_EQ(
      vpi_get(vpiAssertCoverage, vpi_handle_by_name(VpiText("top"), nullptr)),
      0);
}

TEST_F(AssertionControlRun, AnInstanceControlEndsAnAssertionsOwnStop) {
  ASSERT_TRUE(RegisterStopFirst());
  Run("module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  int r;\n"
      "  first: assert property (@(posedge clk) a);\n"
      "  initial begin\n"
      "    $stop_first;\n"
      "    r = $coverage_control(1, 20, 10, \"top\");\n"
      "    r = $coverage_control(0, 20, 10, \"top\");\n"
      "    #1 clk = 1; #1 clk = 0;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle first = TopAssertion("first");
  ASSERT_NE(first, nullptr);

  EXPECT_EQ(g_stop_status, static_cast<int>(CoverageStatus::kOk));
  EXPECT_EQ(vpi_get(vpiCovered, first), 1);
  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, first),
            static_cast<int>(CoverageStatus::kOk));
}

TEST_F(VpiCoverageControlSim, AnAssertionInNoInstanceControlsNothing) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion("top.dut.a1", vpiAssert);

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiAssertCoverage, assertion),
            Status(CoverageStatus::kError));
}

}  // namespace
}  // namespace delta
