#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "model_gate_logic.h"
#include "model_switch_eval.h"

namespace {

// A 1-bit wire settles to a known logic value when aval matches and the
// corresponding bval bit is clear.
bool SettledToKnown(SimFixture& f, std::string_view name, uint64_t expected) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == (expected & 1u) &&
         (v->value.words[0].bval & 1u) == 0u;
}

// A 1-bit wire settles to high-Z when aval is 0 and the bval bit is set.
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

// cmos/rcmos accept delays per the delay3 grammar in §28.9.
TEST(CmosSwitches, CmosAcceptsDelaySpec) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kCmos));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kRcmos));
}

// cmos/rcmos are unidirectional: output is driven from data, never the reverse.
TEST(CmosSwitches, CmosIsNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kCmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kRcmos));
}

// With data=Z the cmos pair cannot drive the output, regardless of controls.
TEST(CmosSwitches, CmosBlocksHighZData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
}

// A conducting cmos drives a clean logic 0 when data=0 — the n-half carries
// the low level through without inversion.
TEST(CmosSwitches, CmosPassesZeroData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
}

// End-to-end: the n-half of a cmos conducts when ncontrol is high, so a
// driven 0 on the data input reaches the output through the production
// lowering and scheduler paths.
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

// Mirror for data=1: the n-half carries the high level to the output.
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

// The p-half of a cmos conducts when pcontrol is low. With the n-half
// off the output still reflects data, proving the composed pair drives
// through either channel.
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

// Both halves closed: nc=0 leaves the n-half non-conducting and pc=1
// leaves the p-half non-conducting, so nothing drives y and it rests at
// high-Z regardless of the data input.
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

// Rcmos must lower and simulate through the same composition rule as
// cmos; pinning the conducting case exercises the shared production
// path end-to-end and guards against a silent divergence.
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

}  // namespace
