#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortKindSimulation, HeaderOutputPortResolvesItsDriversAgainstEachOther) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t(output o);\n"
      "  assign o = 1'b1;\n"
      "  assign o = 1'b0;\n"
      "endmodule\n",
      f, "o");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(PortKindSimulation, BodyWireSpellingResolvesTheSameWay) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t(o);\n"
      "  output o;\n"
      "  wire o;\n"
      "  assign o = 1'b1;\n"
      "  assign o = 1'b0;\n"
      "endmodule\n",
      f, "o");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(PortKindSimulation, HeaderOutputPortReportsItsDriversStrength) {
  SimFixture f;
  std::string out = RunCapture(
      "module t(output o);\n"
      "  assign (pull0, pull1) o = 1'b1;\n"
      "  initial #1 $display(\"[%v]\", o);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Pu1"), std::string::npos) << out;
}

TEST(PortKindSimulation, HeaderOutputWithExplicitDataTypeIsNoNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(output integer o);\n"
      "  initial o = 32'd7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindNet("o"), nullptr);
  auto* var = f.ctx.FindVariable("o");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(PortKindSimulation, HeaderInputPortIsANet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_NE(f.ctx.FindNet("i"), nullptr);
}

TEST(PortKindSimulation, APortWithNoPortKindIsANetOfTheDefaultNetType) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`default_nettype tri0\n"
                           "module s0(input logic a, output logic b);\n"
                           "  assign b = a;\n"
                           "endmodule\n"
                           "module s1(input wire logic a, "
                           "output logic b);\n"
                           "  assign b = a;\n"
                           "endmodule\n"
                           "`default_nettype wire\n"
                           "module s2(input tri1 logic a, "
                           "output logic b);\n"
                           "  assign b = a;\n"
                           "endmodule\n"
                           "module t;\n"
                           "  logic x, y, z;\n"
                           "  s0 u0(.b(x));\n"
                           "  s1 u1(.b(y));\n"
                           "  s2 u2(.b(z));\n"
                           "  initial #1 $display(\"%b %b %b\", x, y, z);\n"
                           "endmodule\n",
                           f),
      "0 z 1\n");
}

}  // namespace
