

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

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

}
