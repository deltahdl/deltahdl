#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConditionalStmtSim, IfThenTakenWhenConditionTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    en = 1'b1;\n"
      "    if (en) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(ConditionalStmtSim, IfThenSkippedWhenConditionFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd7;\n"
      "    en = 1'b0;\n"
      "    if (en) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

TEST(ConditionalStmtSim, IfElseTakesElseWhenFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    en = 1'b0;\n"
      "    if (en) x = 8'd1; else x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}});
}

TEST(ConditionalStmtSim, ElseIfChainSelectsMatchingBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] sel;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    if (sel == 8'd2) x = 8'd20;\n"
      "    else if (sel == 8'd1) x = 8'd10;\n"
      "    else x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}});
}

TEST(ConditionalStmtSim, CondPredicateTripleAmpBothTrueTakesThen) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    if (a &&& b) x = 8'd1; else x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(ConditionalStmtSim, CondPredicateTripleAmpFalseConjunctTakesElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 1'b1;\n"
      "    if (a &&& b) x = 8'd1; else x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}});
}

TEST(ConditionalStmtSim, CondPatternMatchesSelectsThenOnMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd5;\n"
      "    if (v matches 8'd5) x = 8'd1; else x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(ConditionalStmtSim, CondPatternMatchesTakesElseOnMismatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd4;\n"
      "    if (v matches 8'd5) x = 8'd1; else x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}});
}

TEST(ConditionalStmtSim, UniqueIfExecutesMatchingBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] sel;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    unique if (sel == 8'd0) x = 8'd0;\n"
      "    else if (sel == 8'd1) x = 8'd10;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}});
}

TEST(ConditionalStmtSim, PriorityIfExecutesFirstTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] sel;\n"
      "  initial begin\n"
      "    sel = 8'd3;\n"
      "    priority if (sel >= 8'd2) x = 8'd20;\n"
      "    else if (sel >= 8'd1) x = 8'd10;\n"
      "    else x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 20u}});
}

TEST(ConditionalStmtSim, AConditionalOperatorAfterATripleAmpPredicate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd0;\n"
      "    z = x matches 8'd5 &&& y > 0 ? 8'd1 : 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"z", 2u}});
}

}  // namespace
