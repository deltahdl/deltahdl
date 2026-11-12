#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_matches_short_circuit.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IfMatchesSim, MatchesConstantTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, MatchesConstantFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd10) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, PatternZBitsAreNoWildcard) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    if (sel matches 4'b1?1?) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, MatchesWildcardMismatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    if (sel matches 4'b0?1?) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, MatchesWithGuardTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    if (x matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, MatchesWithGuardFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b0;\n"
      "    if (x matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, UnknownGuardTakesElseArm) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'bx;\n"
      "    y = 8'd0;\n"
      "    if (x matches 8'd5 &&& guard) y = 8'd1;\n"
      "    else y = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(IfMatchesSim, FailedClauseSkipsLaterClauseEvaluation) {
  RunMatchesShortCircuitSkipsLaterClause(
      "if (x matches 8'd99 &&& cnt++) y = 8'd1;\n"
      "    else y = 8'd2;");
}

TEST(IfMatchesSim, ElseIfChainMatches) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else if (x matches 8'd10) y = 8'd2;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(IfMatchesSim, MatchesResultIsBool) {
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

TEST(IfMatchesSim, PriorityIfWithMatchesSelectsFirstMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    priority if (x matches 8'd5) y = 8'd1;\n"
      "    else if (x matches 8'd10) y = 8'd2;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(IfMatchesSim, UniqueIfWithMatchesSelectsMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    unique if (x matches 8'd5) y = 8'd1;\n"
      "    else if (x matches 8'd10) y = 8'd2;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(IfMatchesSim, MatchesParameterPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter P = 8'd5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches P) y = 8'd1;\n"
      "    else y = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, MatchesLocalparamPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam LP = 8'd7;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd7;\n"
      "    if (x matches LP) y = 8'd1;\n"
      "    else y = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, MatchesGenvarPattern) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      logic [7:0] x;\n"
                 "      initial begin\n"
                 "        x = 8'd2;\n"
                 "        if (x matches i) out[i] = 8'd30;\n"
                 "        else out[i] = 8'd99;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {99u, 99u, 30u, 99u});
}

TEST(IfMatchesSim, MatchesConstantFunctionCallPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function automatic logic [7:0] five();\n"
      "    five = 8'd5;\n"
      "  endfunction\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches five()) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, TwoMatchesClausesBothSucceed) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd7;\n"
      "    if (x matches 8'd5 &&& y matches 8'd7) z = 8'd1;\n"
      "    else z = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "z");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, SecondMatchesClauseFailsTakesElse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd7;\n"
      "    if (x matches 8'd5 &&& y matches 8'd9) z = 8'd1;\n"
      "    else z = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "z");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(IfMatchesSim, LeadingBooleanFilterThenMatchesTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    if (en &&& x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, LeadingBooleanFilterFalseTakesElse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b0;\n"
      "    if (en &&& x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, MatchesNoElse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd77;\n"
      "    if (x matches 8'd99) y = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 77u);
}

std::string JmpModule(const std::string& value, const std::string& body) {
  return "module t;\n"
         "  typedef union tagged {\n"
         "    bit [9:0] JmpU;\n"
         "    struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
         "  } Jmp;\n"
         "  Jmp e;\n"
         "  int rf [0:3];\n"
         "  int y;\n" +
         body +
         "  initial begin\n"
         "    rf[1] = 3;\n"
         "    e = " +
         value + ";\n    go();\n  end\nendmodule\n";
}

constexpr const char* kJmpTask =
    "  task go();\n"
    "    if (e matches (tagged JmpC '{cc:.c, addr:.a}) &&& (rf[c] != 0))\n"
    "      y = c * 1000 + a;\n"
    "    else if (e matches (tagged JmpU .u) &&& u > 5)\n"
    "      y = u;\n"
    "    else\n"
    "      y = 5;\n"
    "  endtask\n";

TEST(IfMatchesSim, TheFilterAndTheTrueArmReadTheBoundIdentifiers) {
  SimFixture f;
  EXPECT_EQ(
      RunModule(f, JmpModule("tagged JmpC '{1, 77}", kJmpTask).c_str(), "y"),
      1077u);
}

TEST(IfMatchesSim, AValueOfAnotherTagFailsTheClause) {
  SimFixture f;
  EXPECT_EQ(RunModule(f, JmpModule("tagged JmpU (9)", kJmpTask).c_str(), "y"),
            9u);
}

TEST(IfMatchesSim, AFalseFilterAfterAMatchTakesTheElseArm) {
  SimFixture f;
  EXPECT_EQ(
      RunModule(f, JmpModule("tagged JmpC '{2, 77}", kJmpTask).c_str(), "y"),
      5u);
}

TEST(IfMatchesSim, AFunctionBodyReadsTheBoundIdentifiers) {
  SimFixture f;
  EXPECT_EQ(
      RunModule(f,
                JmpModule("tagged JmpC '{1, 77}",
                          "  function void go();\n"
                          "    if (e matches (tagged JmpC '{cc:.c, addr:.a}) "
                          "&&& (rf[c] != 0))\n"
                          "      y = c * 1000 + a;\n"
                          "    else\n"
                          "      y = 5;\n"
                          "  endfunction\n")
                    .c_str(),
                "y"),
      1077u);
}

TEST(IfMatchesSim, ConstantPatternComparesXAndZBits) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v = 4'b1010, w = 'x;\n"
      "  int n = 0;\n"
      "  initial begin\n"
      "    if (v matches 4'b1x1x) n += 1;\n"
      "    if (w matches 4'b0000) n += 10;\n"
      "    if (w matches 4'bxxxx) n += 100;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 100u);
}

TEST(IfMatchesSim, TaggedPatternAgainstAnArrayElement) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt arr [2];\n"
      "  int y = 0;\n"
      "  initial begin\n"
      "    arr[1] = tagged Valid 9;\n"
      "    if (arr[1] matches tagged Valid .n) y = n; else y = -1;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 9u);
}

TEST(IfMatchesSim, StructurePatternAgainstAnArrayElement) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int a; int b; } P;\n"
      "  P arr [2];\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    arr[1] = '{5, 6};\n"
      "    if (arr[1] matches '{.x, .z}) r = x * 10 + z; else r = -1;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 56u);
}

TEST(IfMatchesSim, PriorityIfBindsPatternIdentifiers) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v = tagged Valid 7;\n"
      "  int y;\n"
      "  initial begin\n"
      "    priority if (v matches tagged Valid .n &&& n > 3) y = n;\n"
      "    else y = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

TEST(IfMatchesSim, UniqueIfBindsPatternIdentifiers) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v = tagged Valid 7;\n"
      "  int y;\n"
      "  initial begin\n"
      "    unique if (v matches tagged Invalid) y = 1;\n"
      "    else if (v matches tagged Valid .n &&& n > 3) y = n + 10;\n"
      "    else y = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 17u);
}

TEST(IfMatchesSim, QualifiedIfsBindPatternIdentifiersInAFunction) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v = tagged Valid 7;\n"
      "  int y;\n"
      "  function automatic int f();\n"
      "    int r = 0;\n"
      "    priority if (v matches tagged Valid .n &&& n > 3) r = n;\n"
      "    else r = 0;\n"
      "    unique0 if (v matches tagged Valid .k) r += k * 10;\n"
      "    return r;\n"
      "  endfunction\n"
      "  initial y = f();\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(IfMatchesSim, LaterUniqueConditionReadsTheOuterName) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v = tagged Valid 7;\n"
      "  int n = 0, y;\n"
      "  initial begin\n"
      "    unique if (v matches tagged Valid .n) y = n;\n"
      "    else if (n == 7) y = 100;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(IfMatchesSim, LaterUniqueConditionReadsTheOuterNameInAFunction) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v = tagged Valid 7;\n"
      "  int n = 0, y;\n"
      "  function automatic int f();\n"
      "    int r = 0;\n"
      "    unique if (v matches tagged Valid .n) r = n;\n"
      "    else if (n == 7) r = 100;\n"
      "    return r;\n"
      "  endfunction\n"
      "  initial y = f();\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

std::string RunJumpExample(const char* if_statement) {
  SimFixture f;
  return RunCapture(
      std::string("module t;\n"
                  "  typedef union tagged {\n"
                  "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                  "    union tagged {\n"
                  "      bit [9:0] JmpU;\n"
                  "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
                  "    } Jmp;\n"
                  "  } Instr;\n"
                  "  int rf [0:3];\n"
                  "  Instr e;\n"
                  "  task automatic check;\n") +
          if_statement +
          "  endtask\n"
          "  initial begin\n"
          "    rf = '{0, 10, 20, 30};\n"
          "    e = tagged Add '{5'd1, 5'd2, 5'd3}; check;\n"
          "    e = tagged Jmp (tagged JmpU 10'd100); check;\n"
          "    e = tagged Jmp (tagged JmpC '{2'd1, 10'd7}); check;\n"
          "    e = tagged Jmp (tagged JmpC '{2'd0, 10'd9}); check;\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(IfMatchesExampleSim, TheConditionalJumpExampleBindsBothMembers) {
  EXPECT_EQ(
      RunJumpExample(
          "    if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a})))\n"
          "      $display(\"%0d %0d\", c, a);\n"
          "    else\n"
          "      $display(\"other\");\n"),
      "other\nother\n1 7\n0 9\n");
}

TEST(IfMatchesExampleSim, TheTwoMatchExampleMatchesTheBoundJump) {
  EXPECT_EQ(RunJumpExample("    if (e matches (tagged Jmp .j) &&&\n"
                           "        j matches (tagged JmpC '{cc:.c,addr:.a}))\n"
                           "      $display(\"%0d %0d\", c, a);\n"
                           "    else\n"
                           "      $display(\"other\");\n"),
            "other\nother\n1 7\n0 9\n");
}

TEST(IfMatchesExampleSim, TheFilteredExampleTakesTheElseForRegisterZero) {
  EXPECT_EQ(
      RunJumpExample(
          "    if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))\n"
          "        &&& (rf[c] != 0))\n"
          "      $display(\"%0d %0d\", c, a);\n"
          "    else\n"
          "      $display(\"other\");\n"),
      "other\nother\n1 7\nother\n");
}

TEST(IfMatchesSim, EveryFormOfIfMatchesDecidesInEveryKindOfProcedure) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package pk;\n"
          "  typedef union tagged {\n"
          "    void Invalid;\n"
          "    int Valid;\n"
          "  } VInt;\n"
          "  function automatic int f(VInt v);\n"
          "    if (v matches tagged Valid .n &&& n > 0) return n;\n"
          "    else return -1;\n"
          "  endfunction\n"
          "endpackage\n"
          "import pk::*;\n"
          "function automatic int g(VInt v);\n"
          "  priority if (v matches tagged Valid .n) return n + 100;\n"
          "  else if (v matches tagged Invalid) return 0;\n"
          "endfunction\n"
          "class C;\n"
          "  function int m(VInt v);\n"
          "    unique if (v matches tagged Valid .n) return n * 2;\n"
          "    else return 7;\n"
          "  endfunction\n"
          "endclass\n"
          "interface I;\n"
          "  VInt v;\n"
          "  initial begin\n"
          "    v = tagged Valid 5;\n"
          "    #2 if (v matches tagged Valid .n) $display(\"I %0d\", n);\n"
          "  end\n"
          "endinterface\n"
          "program p;\n"
          "  VInt v;\n"
          "  initial begin\n"
          "    v = tagged Invalid;\n"
          "    #3 if (v matches tagged Valid .n) $display(\"P %0d\", n);\n"
          "    else $display(\"P else\");\n"
          "  end\n"
          "endprogram\n"
          "module t;\n"
          "  I u();\n"
          "  p pp();\n"
          "  task tk(VInt v);\n"
          "    if (v matches tagged Valid .n) $display(\"T %0d\", n);\n"
          "    else $display(\"T invalid\");\n"
          "  endtask\n"
          "  if (1) begin : gb\n"
          "    VInt gv;\n"
          "    initial begin\n"
          "      gv = tagged Valid 9;\n"
          "      #1 if (gv matches tagged Valid .n &&& n == 9) $display(\"G "
          "%0d\", n);\n"
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
      "4 -1 -1 104 8 7\nT invalid\nT 4\nG 9\nI 5\nP else\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
