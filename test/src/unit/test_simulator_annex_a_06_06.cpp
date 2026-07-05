#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

// §A.6.6 end-to-end coverage. The BNF productions of §A.6.6 are syntactic, but
// the conditional_statement they define is consumed by the full pipeline: its
// cond_predicate is a real §A.8.3 expression and each branch is a real §A.6.4
// statement_or_null. These tests build that input from real source syntax and
// run it, observing which branch the parsed/elaborated/lowered if actually took
// — i.e. observing the production being consumed, not merely parsed.

namespace {

// conditional_statement: `if ( cond_predicate ) statement_or_null` with a true
// predicate runs the then-branch. Predicate and body are real dependency
// syntax.
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

// A false predicate leaves the then-branch unexecuted: the prior value
// survives.
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

// The `[ else statement_or_null ]` branch runs when the predicate is false.
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

// `{ else if ( cond_predicate ) statement_or_null }`: at runtime the chain
// selects the first matching arm — here the middle else-if.
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

// cond_predicate ::= expression_or_cond_pattern { &&&
// expression_or_cond_pattern } Both conjuncts true → the then-branch runs.
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

// A false first conjunct makes the whole &&& predicate false → else-branch
// runs.
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

// cond_pattern ::= expression matches pattern. A matching value selects the
// then-branch at runtime.
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

// A non-matching value makes the cond_pattern false → the else-branch runs.
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

// unique_priority ::= unique | unique0 | priority. The optional prefix is
// consumed end-to-end and the qualified if still executes the matching arm.
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

// priority if: the prefix is accepted and the first true arm runs.
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

}  // namespace
