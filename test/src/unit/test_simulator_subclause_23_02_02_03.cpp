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

std::string InheritedPortRun(const std::string& keyword,
                             const std::string& header, const std::string& body,
                             const std::string& top) {
  SimFixture f;
  return RunCapture(keyword + " m(" + header + ");\n" + body +
                        (keyword == "program" ? "  initial #3;\n" : "") +
                        "end" + keyword + "\nmodule t;\n" + top + "endmodule\n",
                    f);
}

constexpr const char* kAnsiHeaderKeywords[] = {"module", "interface",
                                               "program"};

TEST(InheritedAnsiPortRun, LaterNamesInheritAnInputWireDeclaration) {
  for (const char* kw : kAnsiHeaderKeywords) {
    EXPECT_EQ(
        InheritedPortRun(
            kw, "input wire a, b, sel, output logic y",
            "  assign y = sel ? a : b;\n"
            "  initial #1 $display(\"%0d %0d\", $bits(b), $bits(sel));\n",
            "  logic a = 0, b = 1, s = 0;\n  wire y;\n  m u(a, b, s, y);\n"
            "  initial #2 $display(\"%b\", y);\n"),
        "1 1\n1\n")
        << kw;
  }
}

TEST(InheritedAnsiPortRun, ALaterNameInheritsAnOutputVariableAndItsRange) {
  for (const char* kw : kAnsiHeaderKeywords) {
    EXPECT_EQ(InheritedPortRun(kw, "output logic [3:0] a, b",
                               "  initial begin a = 4'd9; b = 4'd10; end\n",
                               "  wire [3:0] x, y;\n  m u(x, y);\n"
                               "  initial #1 $display(\"%0d %0d\", $bits(y), "
                               "y);\n"),
              "4 10\n")
        << kw;
  }
}

TEST(InheritedAnsiPortRun, ALaterNameInheritsAnInputIntVariable) {
  for (const char* kw : kAnsiHeaderKeywords) {
    EXPECT_EQ(
        InheritedPortRun(kw, "input var int a, b",
                         "  initial #1 $display(\"%0d %0d\", $bits(b), b);\n",
                         "  int x = 1, y = -70000;\n  m u(x, y);\n"),
        "32 -70000\n")
        << kw;
  }
}

TEST(InheritedAnsiPortRun, ALaterNameInheritsSigningAndRange) {
  for (const char* kw : kAnsiHeaderKeywords) {
    EXPECT_EQ(
        InheritedPortRun(kw, "input signed [7:0] a, b",
                         "  initial #1 $display(\"%0d %0d\", $bits(b), b);\n",
                         "  logic [7:0] x = 1, y = 8'hF0;\n  m u(x, y);\n"),
        "8 -16\n")
        << kw;
  }
}

TEST(InheritedAnsiPortRun, TheMuxOfTheModulesOverviewFollowsItsSelect) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mux2to1(input wire a, b, sel, output logic y);\n"
                       "  always_comb if (sel) y = a; else y = b;\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic a = 1, b = 0, sel = 1;\n"
                       "  wire y;\n"
                       "  mux2to1 u(a, b, sel, y);\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    sel = 0;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    b = 1;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    sel = 1;\n"
                       "    a = 0;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "    a = 1;\n"
                       "    #1 $display(\"%b\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n0\n1\n0\n1\n");
}

}  // namespace
