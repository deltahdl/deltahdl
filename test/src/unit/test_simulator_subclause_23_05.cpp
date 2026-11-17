#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ExternModuleSimulation, ExternDoesNotInterfereWithSimulation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hAB;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ExternModuleSimulation, WildcardPortsFromExternSimulate) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hCD;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(ExternModuleSimulation, NonAnsiExternWildcardSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module gate(a, b, c, d);\n"
      "module gate(.*);\n"
      "  input a, b, c;\n"
      "  output d;\n"
      "  assign d = a & b & c;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c, d;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  gate u0(.a(a), .b(b), .c(c), .d(d));\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExternModuleSimulation, ValueParameterizedExternWildcardSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module widen #(parameter W = 4)\n"
      "  (input logic [W-1:0] a, output logic [W-1:0] b);\n"
      "module widen(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] a, b;\n"
      "  assign a = 4'hA;\n"
      "  widen u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(ExternModuleSimulation, TypeParameterizedExternWildcardSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module conv #(parameter type TP = logic [7:0])\n"
      "  (input TP a, output TP b);\n"
      "module conv(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'h5A;\n"
      "  conv u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(ExternModuleSimulation, NestedExternModuleSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  module child(input logic [7:0] a, output logic [7:0] b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "  assign a = 8'h3C;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

TEST(ExternModuleSimulation, WildcardExternUnpackedParameterPortIsArray) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module a #(parameter int P [2] = '{3, 5}) (output int y);\n"
      "module a (.*);\n"
      "  assign y = P[1];\n"
      "endmodule\n"
      "module top;\n"
      "  int y;\n"
      "  a u (.y(y));\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

std::string WildcardRun(const std::string& decls, SimFixture& f) {
  return RunCapture(decls +
                        "module t;\n  logic [3:0] a = 4'd5;\n"
                        "  wire [3:0] y;\n  m u(.a(a), .y(y));\n"
                        "  initial #1 $display(\"y %0d\", y);\n"
                        "endmodule\n",
                    f);
}

TEST(ExternWildcardRun, ANonAnsiExternWithParametersFeedsTheHeader) {
  SimFixture f;
  EXPECT_EQ(WildcardRun("extern module m #(parameter W = 4) (a, y);\n"
                        "module m (.*);\n  input [W-1:0] a;\n"
                        "  output [W-1:0] y;\n  assign y = a;\nendmodule\n",
                        f),
            "y 5\n");
}

TEST(ExternWildcardRun, AnExternMacromoduleFeedsTheHeader) {
  SimFixture f;
  EXPECT_EQ(WildcardRun("extern macromodule m (input [3:0] a, "
                        "output [3:0] y);\n"
                        "macromodule m (.*);\n  assign y = a;\nendmodule\n",
                        f),
            "y 5\n");
}

TEST(ExternWildcardRun, AnAutomaticExternFeedsAnAutomaticHeader) {
  SimFixture f;
  EXPECT_EQ(WildcardRun("extern module automatic m (input [3:0] a, "
                        "output [3:0] y);\n"
                        "module automatic m (.*);\n  assign y = a;\n"
                        "endmodule\n",
                        f),
            "y 5\n");
}

TEST(ExternWildcardRun, AnExternWrittenAfterTheModuleFeedsTheHeader) {
  SimFixture f;
  EXPECT_EQ(WildcardRun("module m (.*);\n  assign y = a;\nendmodule\n"
                        "extern module m (input [3:0] a, output [3:0] y);\n",
                        f),
            "y 5\n");
}

TEST(ExternWildcardRun, DISABLED_AnExternImportTypesTheHeadersPorts) {
  SimFixture f;
  EXPECT_EQ(WildcardRun("package p;\n  typedef logic [3:0] t4;\nendpackage\n"
                        "extern module m import p::*; (input t4 a, "
                        "output t4 y);\n"
                        "module m (.*);\n  assign y = a;\nendmodule\n",
                        f),
            "y 5\n");
}

TEST(ExternWildcardRun, AnImportOnBothHeadersTypesThePorts) {
  SimFixture f;
  EXPECT_EQ(WildcardRun("package p;\n  typedef logic [3:0] t4;\nendpackage\n"
                        "extern module m import p::*; (input t4 a, "
                        "output t4 y);\n"
                        "module m import p::*; (input t4 a, output t4 y);\n"
                        "  assign y = a;\nendmodule\n",
                        f),
            "y 5\n");
}

TEST(ExternWildcardRun, DISABLED_ANestedExternFeedsItsNestedHeader) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  logic [3:0] a = 4'd5;\n"
                       "  wire [3:0] y;\n"
                       "  extern module n (input [3:0] a, output [3:0] y);\n"
                       "  module n (.*);\n    assign y = a;\n  endmodule\n"
                       "  n u(.a(a), .y(y));\n"
                       "  initial #1 $display(\"y %0d\", y);\n"
                       "endmodule\n",
                       f),
            "y 5\n");
}

TEST(ExternWildcardRun, ADifferentParameterDefaultIsAccepted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("extern module m #(parameter W = 4) "
                       "(output [7:0] y);\n"
                       "module m #(parameter W = 5) (output [7:0] y);\n"
                       "  assign y = W;\nendmodule\n"
                       "module t;\n  wire [7:0] y;\n  m u(y);\n"
                       "  initial #1 $display(\"y %0d\", y);\nendmodule\n",
                       f),
            "y 5\n");
}

TEST(ExternTopRun, DISABLED_ANonAnsiExternBesideItsDefinitionIsNoTop) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops("extern module m (a, b);\n"
                              "module m (a, b);\n  input a;\n  output b;\n"
                              "  initial $display(\"%m\");\nendmodule\n",
                              f),
            "m\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
