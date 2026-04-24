// §28.7

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// Return true when the 1-bit wire ``name`` settled to a known logic value
// equal to ``expected`` (aval matches, bval is 0 meaning no x/z bits).
bool SettledToKnown(SimFixture& f, std::string_view name, uint64_t expected) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == (expected & 1u) &&
         (v->value.words[0].bval & 1u) == 0u;
}

// Return true when the 1-bit wire ``name`` settled to high-Z (aval=0, bval=1).
bool SettledToHighZ(SimFixture& f, std::string_view name) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == 0u &&
         (v->value.words[0].bval & 1u) == 1u;
}

// nmos conducts when control is 1; a driven data=0 reaches the output.
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

// nmos conducts when control is 1; a driven data=1 reaches the output.
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

// nmos is non-conducting when control is 0; output goes to high-Z
// regardless of data value.
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

// pmos polarity is the mirror of nmos: it conducts on control=0.
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

// Table 28-6 groups rnmos with nmos: a conducting rnmos must produce the
// same logic output as a conducting nmos for deterministic controls.
// Strength attenuation is a separate concern (§28.14).
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

// Table 28-6 groups rpmos with pmos.
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

// §28.7 says the four switches are unidirectional channels for data.
// Running two sibling switches with swapped input sources must produce
// distinct outputs on their respective output terminals — confirming the
// simulator wires data only into the output (terms[0]) and never back
// from the output into the data/control inputs.
TEST(MosSwitchSimulation, OutputFollowsDataOnlyWhenConducting) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y_on, y_off;\n"
      "  wire d, c_on, c_off;\n"
      "  assign d = 1'b1;\n"
      "  assign c_on = 1'b1;\n"
      "  assign c_off = 1'b0;\n"
      "  nmos g_on(y_on, d, c_on);\n"
      "  nmos g_off(y_off, d, c_off);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y_on", 1u));
  EXPECT_TRUE(SettledToHighZ(f, "y_off"));
  EXPECT_TRUE(SettledToKnown(f, "d", 1u));
  EXPECT_TRUE(SettledToKnown(f, "c_on", 1u));
  EXPECT_TRUE(SettledToKnown(f, "c_off", 0u));
}

// Table 28-6 blocking row: when control is 0 the nmos output is high-Z
// regardless of data. This case pairs with NmosBlocksOutputWhenControlLow
// (which uses data=1) to close the ctrl=0 row of the nmos table.
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

// Table 28-6 cell (D=x, C=1): a conducting nmos passes the unknown data
// value through to the output.
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
  // x is encoded aval=1, bval=1 in the 4-value rails.
  EXPECT_EQ(v->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(v->value.words[0].bval & 1u, 1u);
}

// Table 28-6 cell (D=z, C=1) for nmos: a conducting switch with a high-Z
// data value yields a high-Z output — production selects the data arm and
// the arm's z bit propagates unchanged.
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

// Table 28-6 cell (D=0, C=1) for pmos blocks: pmos conducts on control=0,
// so control=1 with any data gives high-Z. Pairs with
// PmosBlocksOutputWhenControlHigh (data=1) to close the pmos ctrl=1 row.
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

}  // namespace
