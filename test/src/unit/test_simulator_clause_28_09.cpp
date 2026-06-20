#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "model_gate_logic.h"
#include "model_switch_eval.h"

namespace {

bool SettledToKnown(SimFixture& f, std::string_view name, uint64_t expected) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == (expected & 1u) &&
         (v->value.words[0].bval & 1u) == 0u;
}

bool SettledToHighZ(SimFixture& f, std::string_view name) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == 0u &&
         (v->value.words[0].bval & 1u) == 1u;
}

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

}  // namespace
