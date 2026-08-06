#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_switch_settle.h"
#include "model_gate_logic.h"
#include "model_switch_eval.h"

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

// rcmos passes a low data value through its conducting n-channel half, observed
// end to end through the elaborated-and-simulated design rather than a helper.
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

// The p-channel half of rcmos conducts when its control is low, passing the
// data value to the output through the real simulator path.
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

// When the data input is high-impedance and a half conducts, the cmos output is
// high-impedance too — exercised through the simulator rather than the helper.
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

// §28.9 states two distinct strength behaviors for the two CMOS switch flavors:
// the rcmos gate reduces the strength of the signal passing through it per the
// resistive rules of §28.14, whereas the plain cmos gate alters strength in
// only the single supply-drive case of §28.13. The two tests below observe that
// distinction end to end through the elaborated-and-simulated design. The same
// strong data drive is forwarded by each gate: the rcmos knocks it down to pull
// (Table 28-8's Strong->Pull row, reached via the shared ReduceResistive that
// §28.14 owns) while the cmos leaves it strong (ReduceNonresistive, §28.13).
// That the two gates diverge on an identical input is what confirms §28.9's
// rcmos-is-resistive / cmos-is-not classification is the rule being applied,
// rather than any property of the drive or the switch's value semantics.
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

// §28.9 fixes how the switch's delay specification maps onto output
// transitions: with three delays the first is the rise delay, the second the
// fall delay, and the third the delay to z; two delays give rise then fall; a
// lone delay governs every transition; and with no delay specification the
// switch has no propagation delay. The helper elaborates and simulates a
// cmos/rcmos switch held conducting (n-channel enabled) while its data input is
// toggled from an initial block, and returns the time the output settled -- the
// last scheduled event is the switch output, so the final scheduler time is the
// delay production applied. This drives the real lowering + delay-selection
// path, not a reference model.
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

// Boundary/negative form: no delay specification means the switch adds no
// propagation delay, so the output settles in the same time step as the data
// change rather than at a later time.
TEST(CmosSwitches, CmosNoDelaySpecPropagatesWithoutDelay) {
  uint64_t t =
      CmosSettleTime("cmos g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 20u);
}

// rcmos carries the identical delay form; a lone delay governs each edge.
TEST(CmosSwitches, RcmosSingleDelayAppliesToEveryTransition) {
  EXPECT_EQ(CmosSettleTime("rcmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            27u);
}

}  // namespace
