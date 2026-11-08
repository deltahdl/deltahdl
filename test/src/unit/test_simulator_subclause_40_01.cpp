#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_preprocessor.h"
#include "fixture_simulator.h"
#include "helpers_fsm_pragma_lexing.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr std::string_view kScope = "$root.tb.unit1";
constexpr int kToggle = 23;

TEST(CoverageApiGeneral, TheApiIsTheBuiltInAccessFunctions) {
  SimFixture f;
  f.ctx.GetCoverageControlState().SetAvailability(std::string(kScope), kToggle,
                                                  CoverageAvailability::kFull);

  auto* control = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, 0), MkInt(f.arena, static_cast<uint64_t>(kToggle)),
       MkInt(f.arena, 11), MkStr(f.arena, kScope)});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(control, f.ctx, f.arena).ToUint64()),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_TRUE(f.ctx.GetCoverageControlState().IsCollecting(std::string(kScope),
                                                           kToggle));

  f.ctx.GetCoverageControlState().SetCoveredItems(std::string(kScope), kToggle,
                                                  12);
  auto* get = MkSysCall(f.arena, "$coverage_get",
                        {MkInt(f.arena, static_cast<uint64_t>(kToggle)),
                         MkInt(f.arena, 11), MkStr(f.arena, kScope)});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(get, f.ctx, f.arena).ToUint64()), 12);
}

TEST(CoverageApiGeneral, TheConstantsArePredefinedByName) {
  PreprocFixture f;
  auto out = Preprocess("`SV_COV_START `SV_COV_TOGGLE `SV_COV_HIER\n", f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(out.find('0'), std::string::npos);
  EXPECT_NE(out.find("23"), std::string::npos);
  EXPECT_NE(out.find("11"), std::string::npos);
}

TEST(CoverageApiGeneral, TheVpiRoutinesControlTheSameCollection) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);

  vpi_ctx.GetCoverageControlState().SetAvailability(
      "top.dut", kToggle, CoverageAvailability::kFull);
  VpiHandle dut = vpi_ctx.CreateModule("dut", "top.dut");

  EXPECT_EQ(vpi_control(vpiCoverageStart, vpiToggleCoverage, dut),
            static_cast<int>(CoverageStatus::kOk));
  EXPECT_TRUE(
      vpi_ctx.GetCoverageControlState().IsCollecting("top.dut", kToggle));

  SetGlobalVpiContext(nullptr);
}

TEST(CoverageApiGeneral, FsmRecognitionReadsThePragma) {
  auto pragmas = CollectFsmPragmas("/* tool state_vector cur_state */");

  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cur_state");
}

TEST(CoverageApiGeneral, TheVpiEnumerationsCarryTheCoverageTypes) {
  EXPECT_NE(vpiAssertCoverage, vpiFsmStateCoverage);
  EXPECT_NE(vpiFsmStateCoverage, vpiStatementCoverage);
  EXPECT_NE(vpiStatementCoverage, vpiToggleCoverage);
  EXPECT_NE(vpiToggleCoverage, vpiAssertCoverage);

  EXPECT_NE(vpiCovered, vpiCoveredCount);
  EXPECT_NE(vpiAssertAttemptCovered, vpiAssertSuccessCovered);
  EXPECT_NE(vpiAssertSuccessCovered, vpiAssertFailureCovered);
}

}  // namespace
