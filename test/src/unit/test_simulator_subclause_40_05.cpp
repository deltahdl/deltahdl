#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_coverage_syscall.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr int kSvCovAssertion = 20;
constexpr int kSvCovStatement = 22;
constexpr int kSvCovToggle = 23;

constexpr int kSvCovHier = 11;

constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);

int RunCoverageGet(SimFixture& f, int coverage_type, std::string_view scope) {
  auto* call = MkSysCall(f.arena, "$coverage_get",
                         {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
                          MkInt(f.arena, kSvCovHier), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

class VpiCoverageExtensions : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.Attach(f_.ctx);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  CoverageControlState& Cov() { return f_.ctx.GetCoverageControlState(); }

  SimFixture f_;
  VpiContext vpi_ctx_;
};

TEST_F(VpiCoverageExtensions, WhatTheSystemFunctionSavedTheVpiMergeLoads) {
  Cov().SetAvailability("top.dut", kSvCovAssertion,
                        CoverageAvailability::kFull);
  ASSERT_EQ(
      RunCoverageSysCall(f_, "$coverage_save", kSvCovAssertion, "run.cov"),
      kOk);

  EXPECT_EQ(vpi_control(vpiCoverageMerge, vpiAssertCoverage, "run.cov"), kOk);
  EXPECT_EQ(Cov().MergeCount("run.cov"), 1u);
}

TEST_F(VpiCoverageExtensions, WhatTheVpiSaveWroteTheSystemFunctionMerges) {
  Cov().SetAvailability("top.dut", kSvCovToggle, CoverageAvailability::kFull);
  ASSERT_EQ(vpi_control(vpiCoverageSave, vpiToggleCoverage, "vpi.cov"), kOk);

  EXPECT_EQ(RunMerge(f_, kSvCovToggle, "vpi.cov"), kOk);
  EXPECT_EQ(Cov().MergeCount("vpi.cov"), 1u);
}

TEST_F(VpiCoverageExtensions, AVpiSaveOfATypeWithNoCoverageStillSavesNothing) {
  Cov().SetAvailability("top.dut", kSvCovToggle, CoverageAvailability::kFull);

  EXPECT_EQ(vpi_control(vpiCoverageSave, vpiStatementCoverage, "vpi.cov"),
            kNoCov);
  EXPECT_EQ(Cov().SaveCount("vpi.cov"), 0u);
}

TEST_F(VpiCoverageExtensions, TheVpiQueryReportsTheCoverageTheLanguageReports) {
  Cov().SetCoverableItems("top.dut", kSvCovStatement, 12);
  Cov().SetCoveredItems("top.dut", kSvCovStatement, 7);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");

  EXPECT_EQ(vpi_get(vpiStatementCoverage, VpiHandleOf(dut)), 7);
  EXPECT_EQ(vpi_get(vpiStatementCoverage, VpiHandleOf(dut)),
            RunCoverageGet(f_, kSvCovStatement, "top.dut"));
}

TEST_F(VpiCoverageExtensions, TheVpiControlResetsWhatTheVpiQueryReports) {
  Cov().SetAvailability("top.dut", kSvCovStatement,
                        CoverageAvailability::kFull);
  Cov().SetCoverableItems("top.dut", kSvCovStatement, 12);
  Cov().SetCoveredItems("top.dut", kSvCovStatement, 7);
  VpiHandle dut = vpi_ctx_.CreateModule("dut", "top.dut");
  ASSERT_EQ(vpi_get(vpiStatementCoverage, VpiHandleOf(dut)), 7);

  ASSERT_EQ(vpi_control(vpiCoverageReset, vpiStatementCoverage, dut), kOk);

  EXPECT_EQ(vpi_get(vpiStatementCoverage, VpiHandleOf(dut)), kNoCov);
  EXPECT_EQ(RunCoverageGet(f_, kSvCovStatement, "top.dut"), kNoCov);
}

}  // namespace
}  // namespace delta
