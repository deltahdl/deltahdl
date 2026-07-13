#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_switch_settle.h"

using namespace delta;

namespace {

TEST(MosSwitchSimulation, NmosConductsDataLowWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(MosSwitchSimulation, NmosConductsDataHighWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, NmosBlocksOutputWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, PmosConductsDataLowWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(MosSwitchSimulation, PmosConductsDataHighWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, PmosBlocksOutputWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, RnmosConductsDataWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, RnmosBlocksOutputWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, RpmosConductsDataWhenControlLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(MosSwitchSimulation, RpmosBlocksOutputWhenControlHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, NmosBlocksOutputWithLowDataAndControl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b0;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(MosSwitchSimulation, NmosPassesUnknownDataWhenConducting) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'bx;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("y");
  ASSERT_NE(v, nullptr);

  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

TEST(MosSwitchSimulation, NmosPassesHighZDataWhenConducting) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'bz;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

// §28.7 states an nmos/pmos switch passes the strength of the data input to
// the output, changed in only one case — the supply-to-strong reduction
// defined in §28.13. These two tests observe that production behavior end to
// end: a non-supply data strength reaches the output untouched, while a supply
// data strength is the lone case that is reduced (to strong).
TEST(MosSwitchSimulation, NmosPassesPullDataStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(MosSwitchSimulation, NmosReducesSupplyDataStrengthToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

// §28.7 also distinguishes the resistive switches: rnmos/rpmos reduce the
// strength of every signal they pass (the reduction itself is §28.14's). Here
// the same strong data that an nmos would forward unchanged is knocked down to
// pull when it passes through an rnmos, observing that resistive routing.
TEST(MosSwitchSimulation, RnmosReducesStrongDataStrengthToPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

// §28.7's strength statements name nmos and pmos together as the switches that
// alter strength in only one case. The pmos half is exercised here: a pull data
// strength (not the lone supply case) reaches the output untouched when it
// conducts on a low control.
TEST(MosSwitchSimulation, PmosPassesPullDataStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

// The "only one case" for pmos: a supply data strength is the lone strength the
// switch alters, dropping to strong. Completes the pmos half of §28.7's
// nmos/pmos strength statement alongside the pull-passthrough case above.
TEST(MosSwitchSimulation, PmosReducesSupplyDataStrengthToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

// The resistive statement likewise names rnmos and rpmos together. The rpmos
// half mirrors the rnmos case above: strong data is knocked down to pull as it
// passes through, observing that rpmos routes resistively too.
TEST(MosSwitchSimulation, RpmosReducesStrongDataStrengthToPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(MosSwitchSimulation, PmosBlocksOutputWithLowDataAndHighControl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b0;\n"
      "  assign c = 1'b1;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

// Table 28-6's control=x and control=z columns use the ambiguous L/H result
// symbols (0-or-z, 1-or-z): when the control is not a clean 0/1 the switch
// cannot be relied on to forward a definite logic level. These observe that an
// unknown or high-impedance control yields a high-impedance output rather than
// passing the data value through.
TEST(MosSwitchSimulation, NmosControlUnknownDoesNotPassDefiniteValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'bx;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // Ambiguous control: the switch passes "1 or z", which collapses in the
  // ternary (§11.4.11) to x = (aval=1, bval=1), not a definite value.
  auto* v = f.ctx.FindVariable("y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

TEST(MosSwitchSimulation, NmosControlHighZDoesNotPassDefiniteValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign d = 1'b1;\n"
      "  assign c = 1'bz;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // Floating (z) control behaves like x control: passes "1 or z", which
  // collapses in the ternary (§11.4.11) to x = (aval=1, bval=1).
  auto* v = f.ctx.FindVariable("y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

}  // namespace
