#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_switch_settle.h"
#include "model_switch_eval.h"
#include "model_val4.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(CmosSwitches, CmosIsNmosPlusPmos) {
  EXPECT_NE(EvalMosSwitch(SwitchType::kCmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, RcmosIsRnmosPlusRpmos) {
  EXPECT_NE(EvalMosSwitch(SwitchType::kRcmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, CmosMaxThreeDelays) {
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kCmos), 3u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kRcmos), 3u);
}

TEST(CmosSwitches, CmosAcceptsDelaySpec) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kCmos));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kRcmos));
}

TEST(CmosSwitches, CmosIsNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kCmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kRcmos));
}

TEST(CmosSwitches, CmosBlocksHighZData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, CmosPassesZeroData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
}

TEST(CmosSwitches, CmosPassesDataLowWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(CmosSwitches, CmosPassesDataHighWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, CmosPassesDataLowWhenPcontrolLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b0;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(CmosSwitches, CmosPassesDataHighWhenPcontrolLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b0;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, CmosBlocksOutputWhenBothHalvesOff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(CmosSwitches, RcmosPassesDataWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, RcmosBlocksOutputWhenBothHalvesOff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(CmosSwitches, RcmosPassesDataLowWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(CmosSwitches, RcmosPassesDataHighWhenPcontrolLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b0;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, CmosPassesHighZDataAsHighZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'bz;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(CmosSwitches, RcmosReducesForwardedStrengthPerResistiveRule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(CmosSwitches, CmosLeavesForwardedNonSupplyStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

uint64_t CmosSettleTime(const std::string& decl, const std::string& stim) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  logic src, nc, pc;\n  " + decl +
                    "\n  initial begin " + stim + " end\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.scheduler.CurrentTime().ticks;
}

TEST(CmosSwitches, CmosRiseDelayGovernsZeroToOne) {
  uint64_t t =
      CmosSettleTime("cmos #(5, 10, 15) g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 25u);
}

TEST(CmosSwitches, CmosFallDelayGovernsOneToZero) {
  uint64_t t =
      CmosSettleTime("cmos #(5, 10, 15) g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b1; #20 src = 1'b0;");
  EXPECT_EQ(t, 30u);
}

TEST(CmosSwitches, CmosTwoDelaysUseRiseThenFall) {
  EXPECT_EQ(CmosSettleTime("cmos #(5, 10) g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            25u);
  EXPECT_EQ(CmosSettleTime("cmos #(5, 10) g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b1; #20 src = 1'b0;"),
            30u);
}

TEST(CmosSwitches, CmosSingleDelayAppliesToEveryTransition) {
  EXPECT_EQ(CmosSettleTime("cmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            27u);
  EXPECT_EQ(CmosSettleTime("cmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b1; #20 src = 1'b0;"),
            27u);
}

TEST(CmosSwitches, CmosNoDelaySpecPropagatesWithoutDelay) {
  uint64_t t =
      CmosSettleTime("cmos g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 20u);
}

TEST(CmosSwitches, RcmosSingleDelayAppliesToEveryTransition) {
  EXPECT_EQ(CmosSettleTime("rcmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            27u);
}

TEST(CmosSwitchSim, AnUnknownControlDrivesTheLOrHOfThePairedSwitches) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic d0 = 0, d1 = 1, dz = 1'bz, nx = 1'bx, poff = 1, px = 1'bx;\n"
      "  wire y1, y2, y3;\n"
      "  cmos (y1, d0, nx, poff);\n"
      "  cmos (y2, d1, nx, px);\n"
      "  cmos (y3, dz, nx, px);\n"
      "  initial #1 $display(\"%v %v %b\", y1, y2, y3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "StL StH z\n");
}

}  // namespace
