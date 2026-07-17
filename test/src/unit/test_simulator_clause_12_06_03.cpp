

#include "fixture_simulator.h"
#include "helpers_matches_short_circuit.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TernaryMatchesSim, TernaryMatchesTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = (x matches 8'd5) ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryMatchesSim, TernaryMatchesFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = (x matches 8'd99) ? 8'd42 : 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TernaryMatchesSim, TernaryMatchesWildcard) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    y = (sel matches 4'b1?1?) ? 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(TernaryMatchesSim, TernaryMatchesGuardTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    y = (x matches 8'd5 &&& en) ? 8'd10 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(TernaryMatchesSim, TernaryMatchesGuardFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b0;\n"
      "    y = (x matches 8'd5 &&& en) ? 8'd10 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §12.6.3: a conditional-expression predicate may join several matches clauses
// with `&&&`, and all of them must succeed for the predicate to be true. When
// both matches clauses succeed the predicate is true and the consequent e2 is
// selected.
TEST(TernaryMatchesSim, AllChainedClausesSucceedSelectsConsequent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    y = (a matches 8'd1 &&& b matches 8'd2) ? 8'd7 : 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §12.6.3: all predicate clauses must succeed for the predicate to be true.
// Here the first matches clause succeeds but a later matches clause fails, so
// the whole predicate is false and the alternative e3 is selected even though
// an earlier clause matched.
TEST(TernaryMatchesSim, ChainedLaterClauseFailureSelectsAlternative) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd5;\n"
      "    y = (a matches 8'd1 &&& b matches 8'd2) ? 8'd7 : 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// §12.6.3: the predicate e1 of a conditional expression is a sequential
// conjunction evaluated left to right; once a clause fails, the clauses to its
// right are not evaluated. Here the matches clause fails, so the side-effecting
// filter after `&&&` must not run and the counter it would bump stays at zero.
TEST(TernaryMatchesSim, FailedClauseSkipsLaterClauseEvaluation) {
  RunMatchesShortCircuitSkipsLaterClause(
      "y = (x matches 8'd99 &&& cnt++) ? 8'd1 : 8'd2;");
}

// §12.6.3: a `matches` clause in a conditional-expression predicate carries a
// pattern, and that pattern may be any §11.2.1 constant expression, not only an
// inline literal. Here the pattern is a parameter, which resolves through a
// different evaluation path than a literal. The value matches, so the predicate
// is true and the consequent e2 is selected (y==42); had the parameter resolved
// to a non-matching value the alternative e3 (0) would have been selected, so
// y==42 proves the parameter's value drove the match.
TEST(TernaryMatchesSim, TernaryMatchesParameterPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 8'd5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = (x matches P) ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.6.3: same rule, with the constant-expression pattern produced by a
// localparam. localparam resolution is a distinct path from a parameter or an
// inline literal; the consequent e2 (42) is selected, confirming the
// localparam's value was matched against the predicate value.
TEST(TernaryMatchesSim, TernaryMatchesLocalparamPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam LP = 8'd7;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd7;\n"
      "    y = (x matches LP) ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.6.3: the pattern of a conditional-expression `matches` clause may be a
// genvar, which is constant within a loop generate. Built from real
// generate/genvar syntax and driven through the full pipeline: each unrolled
// iteration matches its value against the genvar pattern, so only the iteration
// whose genvar equals the tested value (2) selects the consequent e2.
// out[2]==30 while the others select the alternative e3, proving the genvar's
// per-iteration value drove the match rather than a literal.
TEST(TernaryMatchesSim, TernaryMatchesGenvarPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] out [0:3];\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "      logic [7:0] x;\n"
      "      initial begin\n"
      "        x = 8'd2;\n"
      "        out[i] = (x matches i) ? 8'd30 : 8'd99;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("out[0]");
  auto* e2 = f.ctx.FindVariable("out[2]");
  auto* e3 = f.ctx.FindVariable("out[3]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e2, nullptr);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 99u);
  EXPECT_EQ(e2->value.ToUint64(), 30u);
  EXPECT_EQ(e3->value.ToUint64(), 99u);
}

// §12.6.3: the constant-expression pattern may also be a constant function
// call, the last §11.2.1 constant form. The value the function returns drives
// the match. Built from real function syntax: five() returns 5, x is 5, so the
// clause holds, the predicate is true, and the consequent e2 (42) is selected.
TEST(TernaryMatchesSim, TernaryMatchesConstantFunctionCallPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic logic [7:0] five();\n"
      "    five = 8'd5;\n"
      "  endfunction\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = (x matches five()) ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.6.3: a predicate clause may be a Boolean filter in the leading position,
// not only after a matches clause. Here the first clause is a Boolean filter
// and the second is a matches clause. Both hold, so the conjunction is true and
// the consequent e2 (42) is selected. The pre-existing guard tests only place
// the filter after the matches clause; this exercises the leading-filter form.
TEST(TernaryMatchesSim, TernaryLeadingBooleanFilterThenMatches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    y = (en &&& x matches 8'd5) ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.6.3: a conditional expression is an expression and can appear wherever an
// expression is expected, not only as a procedural-assignment right-hand side.
// Here the pattern-matching conditional expression is the right-hand side of a
// continuous assignment driving a net-like signal. The predicate holds, so the
// consequent e2 (42) propagates to y, confirming the matches predicate selects
// the conditional-expression branch in this syntactic position too.
TEST(TernaryMatchesSim, TernaryMatchesInContinuousAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial x = 8'd5;\n"
      "  assign y = (x matches 8'd5) ? 8'd42 : 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.6.3: a conditional expression may also appear as a variable declaration
// initializer. A declaration initializer is evaluated as an assignment when the
// variable is created, so the pattern-matching predicate runs in that position
// and drives the branch selection. The predicate holds, so y initializes to the
// consequent e2 (42) rather than the alternative e3 (0), confirming the matches
// predicate is applied in the declaration-initializer position too.
TEST(TernaryMatchesSim, TernaryMatchesInDeclarationInitializer) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] y = (8'd5 matches 8'd5) ? 8'd42 : 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.6.3: the predicate e1 can evaluate to an ambiguous value. A matches
// clause always yields a defined 1-bit result, but a Boolean filter joined by
// `&&&` can be unknown. Here the matches clause holds while the trailing
// Boolean filter is x, so the conjunction does not reach a determined true and
// the predicate does not hold; the alternative e3 (99) is selected rather than
// the consequent e2 (10). This exercises the unknown-filter input form,
// distinct from a filter that is a determined 0.
TEST(TernaryMatchesSim, TernaryMatchesUnknownFilterSelectsAlternative) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'bx;\n"
      "    y = (x matches 8'd5 &&& guard) ? 8'd10 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
