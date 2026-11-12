#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_matches_short_circuit.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TernaryMatchesSim, TernaryMatchesTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = x matches 8'd5 ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = x matches 8'd99 ? 8'd42 : 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TernaryMatchesSim, PatternZBitsAreNoWildcard) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    y = sel matches 4'b1?1? ? 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TernaryMatchesSim, TernaryMatchesGuardTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    y = x matches 8'd5 &&& en ? 8'd10 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(TernaryMatchesSim, TernaryMatchesGuardFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b0;\n"
      "    y = x matches 8'd5 &&& en ? 8'd10 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TernaryMatchesSim, AllChainedClausesSucceedSelectsConsequent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    y = a matches 8'd1 &&& b matches 8'd2 ? 8'd7 : 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(TernaryMatchesSim, ChainedLaterClauseFailureSelectsAlternative) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd5;\n"
      "    y = a matches 8'd1 &&& b matches 8'd2 ? 8'd7 : 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(TernaryMatchesSim, FailedClauseSkipsLaterClauseEvaluation) {
  RunMatchesShortCircuitSkipsLaterClause(
      "y = x matches 8'd99 &&& cnt++ ? 8'd1 : 8'd2;");
}

TEST(TernaryMatchesSim, TernaryMatchesParameterPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter P = 8'd5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = x matches P ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesLocalparamPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam LP = 8'd7;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd7;\n"
      "    y = x matches LP ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesGenvarPattern) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = 8'd2;\n"
                 "        out[i] = x matches i ? 8'd30 : 8'd99;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {99u, 99u, 30u, 99u});
}

TEST(TernaryMatchesSim, TernaryMatchesConstantFunctionCallPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function automatic logic [7:0] five();\n"
      "    five = 8'd5;\n"
      "  endfunction\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = x matches five() ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryLeadingBooleanFilterThenMatches) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    y = en &&& x matches 8'd5 ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesInContinuousAssign) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial x = 8'd5;\n"
      "  assign y = x matches 8'd5 ? 8'd42 : 8'd0;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesInDeclarationInitializer) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] y = 8'd5 matches 8'd5 ? 8'd42 : 8'd0;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesUnknownFilterCombinesBothResults) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'bx;\n"
      "    y = x matches 8'd5 &&& guard ? 8'd10 : 8'd99;\n"
      "    ok = y === 8'b0xx0_x01x;\n"
      "  end\n"
      "endmodule\n",
      f, "ok");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(TernaryMatchesSim, TheConsequentReadsTheBoundIdentifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o;\n"
      "  int some, none;\n"
      "  initial begin\n"
      "    o = tagged Some (42);\n"
      "    some = o matches (tagged Some .x) ? x : -1;\n"
      "    o = tagged None;\n"
      "    none = o matches (tagged Some .x) ? x : -1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* some = f.ctx.FindVariable("some");
  auto* none = f.ctx.FindVariable("none");
  ASSERT_NE(some, nullptr);
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(some->value.ToUint64(), 42u);
  EXPECT_EQ(none->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(TernaryMatchesSim, ConstantPatternComparesXAndZBits) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v = 4'b1010, w = 'x;\n"
      "  int n = 0;\n"
      "  initial begin\n"
      "    n += v matches 4'b1x1x ? 1 : 0;\n"
      "    n += w matches 4'b0000 ? 10 : 0;\n"
      "    n += w matches 4'bxxxx ? 100 : 0;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 100u);
}

TEST(TernaryMatchesSim, AmbiguousClauseSequenceCombinesBothResults) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; bit [7:0] Valid; } VInt;\n"
      "  VInt v = tagged Valid 8'h0F;\n"
      "  logic f = 1'bx;\n"
      "  logic [7:0] r, s;\n"
      "  int ok = 0;\n"
      "  initial begin\n"
      "    r = v matches tagged Valid .* &&& f ? 8'h0F : 8'hF0;\n"
      "    s = v matches tagged Valid .n &&& f ? n : 8'hF0;\n"
      "    ok = (r === 8'bxxxx_xxxx) + 10 * (s === 8'bxxxx_xxxx);\n"
      "  end\n"
      "endmodule\n",
      f, "ok");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 11u);
}

TEST(TernaryMatchesSim, BindingConditionalResultTypeIsBothOperands) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v = tagged Valid (-1);\n"
      "  VInt w = tagged Invalid;\n"
      "  logic [63:0] r, s;\n"
      "  int ok = 0;\n"
      "  initial begin\n"
      "    r = v matches tagged Valid .n ? n : 8'd0;\n"
      "    s = w matches tagged Valid .k ? k : -8'sd1;\n"
      "    ok = (r == 64'h0000_0000_ffff_ffff) + 10 * (s == '1);\n"
      "  end\n"
      "endmodule\n",
      f, "ok");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 11u);
}

TEST(TernaryMatchesSim, TheConditionalOperatorMatchesInEveryKindOfProcedure) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package pk;\n"
          "  typedef union tagged {\n"
          "    void Invalid;\n"
          "    int Valid;\n"
          "  } VInt;\n"
          "  function automatic int f(VInt v);\n"
          "    return v matches tagged Valid .n &&& n > 0 ? n : -1;\n"
          "  endfunction\n"
          "endpackage\n"
          "import pk::*;\n"
          "function automatic int g(VInt v);\n"
          "  return v matches tagged Valid .n ? n + 100 : 0;\n"
          "endfunction\n"
          "class C;\n"
          "  function int m(VInt v);\n"
          "    return v matches tagged Valid .n ? n * 2 : 7;\n"
          "  endfunction\n"
          "endclass\n"
          "interface I;\n"
          "  VInt v;\n"
          "  initial begin\n"
          "    v = tagged Valid 5;\n"
          "    #2 $display(\"I %0d\", v matches tagged Valid .n ? n : 0);\n"
          "  end\n"
          "endinterface\n"
          "program p;\n"
          "  VInt v;\n"
          "  initial begin\n"
          "    v = tagged Invalid;\n"
          "    #3 $display(\"P %0d\", v matches tagged Valid .n ? n : 0);\n"
          "  end\n"
          "endprogram\n"
          "module t;\n"
          "  I u();\n"
          "  p pp();\n"
          "  task tk(VInt v);\n"
          "    $display(\"T %0d\", v matches tagged Valid .n ? n : -5);\n"
          "  endtask\n"
          "  if (1) begin : gb\n"
          "    VInt gv;\n"
          "    initial begin\n"
          "      gv = tagged Valid 9;\n"
          "      #1 $display(\"G %0d\", gv matches tagged Valid .n &&& n == 9 "
          "? n : 0);\n"
          "    end\n"
          "  end\n"
          "  initial begin\n"
          "    C c;\n"
          "    VInt a, b, z;\n"
          "    c = new;\n"
          "    a = tagged Valid 4;\n"
          "    b = tagged Valid -2;\n"
          "    z = tagged Invalid;\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d\", f(a), f(b), f(z), g(a), "
          "c.m(a), c.m(z));\n"
          "    tk(z);\n"
          "    tk(a);\n"
          "  end\n"
          "endmodule\n",
          f),
      "4 -1 -1 104 8 7\nT -5\nT 4\nG 9\nI 5\nP 0\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
