

#include "fixture_simulator.h"
#include "helpers_matches_short_circuit.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IfMatchesSim, MatchesConstantTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
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

TEST(IfMatchesSim, MatchesConstantFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd10) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, MatchesWildcardPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    if (sel matches 4'b1?1?) y = 8'd1;\n"
      "    else y = 8'd0;\n"
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

TEST(IfMatchesSim, MatchesWildcardMismatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    if (sel matches 4'b0?1?) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, MatchesWithGuardTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IfMatchesSim, MatchesWithGuardFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §12.6.2: a matches clause always yields a defined 1-bit result, but a Boolean
// filter joined with `&&&` can leave the overall predicate ambiguous. The
// standard if-else rule then applies: the true arm runs only on a determined
// nonzero result, so an unknown filter steers control to the else arm.
TEST(IfMatchesSim, UnknownGuardTakesElseArm) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.6.2: the predicate is a sequential conjunction evaluated left to right;
// once a clause fails, the clauses to its right are not evaluated. Here the
// matches clause fails, so the side-effecting Boolean filter after `&&&` must
// not run and the counter it would bump stays at its initial value.
TEST(IfMatchesSim, FailedClauseSkipsLaterClauseEvaluation) {
  RunMatchesShortCircuitSkipsLaterClause(
      "if (x matches 8'd99 &&& cnt++) y = 8'd1;\n"
      "    else y = 8'd2;");
}

TEST(IfMatchesSim, ElseIfChainMatches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else if (x matches 8'd10) y = 8'd2;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(IfMatchesSim, MatchesResultIsBool) {
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

// §12.6.2: the priority and unique qualifiers can be used even when the
// if-else predicate uses pattern matching. A priority if selects the first
// matching arm, here the second.
TEST(IfMatchesSim, PriorityIfWithMatchesSelectsFirstMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    priority if (x matches 8'd5) y = 8'd1;\n"
      "    else if (x matches 8'd10) y = 8'd2;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.6.2: a unique if whose arms use pattern matching still selects the single
// matching arm.
TEST(IfMatchesSim, UniqueIfWithMatchesSelectsMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    unique if (x matches 8'd5) y = 8'd1;\n"
      "    else if (x matches 8'd10) y = 8'd2;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.6.2: a clause of the predicate has the form `expression matches pattern`,
// and the pattern may be a constant-expression drawn from any of the §11.2.1
// constant forms, not only an inline literal. Here the pattern is a parameter,
// which resolves through a different evaluation path than a literal. The value
// matches, so the true arm runs and y becomes 1; if the parameter had resolved
// to 0 the match would fail and the else arm (y=2) would run instead, so y==1
// proves the parameter's value drove the match.
TEST(IfMatchesSim, MatchesParameterPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 8'd5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches P) y = 8'd1;\n"
      "    else y = 8'd2;\n"
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

// §12.6.2: same rule, with the constant-expression pattern produced by a
// localparam. localparam resolution is a distinct path from a parameter or an
// inline literal; y==1 confirms the localparam's value was matched against the
// predicate value.
TEST(IfMatchesSim, MatchesLocalparamPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam LP = 8'd7;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd7;\n"
      "    if (x matches LP) y = 8'd1;\n"
      "    else y = 8'd2;\n"
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

// §12.6.2: the pattern of a `matches` clause may be any §11.2.1 constant
// expression, including a genvar, which is constant within a loop generate.
// Built from real generate/genvar syntax and driven through the full pipeline:
// each unrolled iteration matches its value against the genvar pattern, so only
// the iteration whose genvar equals the tested value (2) takes the true arm.
// out[2]==30 while the others take the else arm, proving the genvar's
// per-iteration value drove the match rather than a literal.
TEST(IfMatchesSim, MatchesGenvarPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
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

// §12.6.2: the constant-expression pattern may also be a constant function
// call, the last §11.2.1 constant form. The value the function returns drives
// the match. Built from real function syntax: five() returns 5, x is 5, so the
// clause holds and the true arm runs (y==1). If the call had returned something
// else the else arm would run, so y==1 shows the call result drove the match.
TEST(IfMatchesSim, MatchesConstantFunctionCallPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.6.2: the predicate is a series of clauses, and a clause other than the
// first may itself be a `matches` clause rather than a Boolean filter. Two
// matches clauses joined by `&&&` form a sequential conjunction; when both
// succeed the whole predicate is true and the true arm runs. z==1 (not the
// else value 2) shows both matches clauses were evaluated and both held.
TEST(IfMatchesSim, TwoMatchesClausesBothSucceed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd7;\n"
      "    if (x matches 8'd5 &&& y matches 8'd7) z = 8'd1;\n"
      "    else z = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("z");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.6.2: all clauses of the predicate shall succeed for it to be true. Here
// the first matches clause holds but the second matches clause fails, so the
// conjunction is false and control goes to the else arm. z==2 confirms a later
// matches clause gates the predicate just as the first one does.
TEST(IfMatchesSim, SecondMatchesClauseFailsTakesElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd7;\n"
      "    if (x matches 8'd5 &&& y matches 8'd9) z = 8'd1;\n"
      "    else z = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("z");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.6.2: a clause of the predicate may be a Boolean filter in any position,
// not only after a matches clause. Here the leading clause is a Boolean filter
// and the second clause is a matches clause. Both hold, so the conjunction is
// true and the true arm runs (y==1).
TEST(IfMatchesSim, LeadingBooleanFilterThenMatchesTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.6.2: all clauses of the predicate shall succeed. Here the leading Boolean
// filter is false, so the conjunction fails regardless of the trailing matches
// clause (which does hold), and control goes to the else arm (y==0). This shows
// a Boolean-filter clause gates the predicate from the leading position too.
TEST(IfMatchesSim, LeadingBooleanFilterFalseTakesElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IfMatchesSim, MatchesNoElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = 8'd77;\n"
      "    if (x matches 8'd99) y = 8'd1;\n"
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

}  // namespace
