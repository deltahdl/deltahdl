#include "builders_ast.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

inline Expr* MakeTernary(Arena& arena, Expr* cond, Expr* t, Expr* f) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kTernary;
  e->condition = cond;
  e->true_expr = t;
  e->false_expr = f;
  return e;
}

inline Expr* MakeAssignExpr(Arena& arena, const char* name, uint64_t val) {
  return MakeBinary(arena, TokenKind::kEq, MakeId(arena, name),
                    MakeInt(arena, val));
}

TEST(ConditionalAmbiguousCondition, ZConditionCombinesBranchesBitwise) {
  SimFixture f;

  MakeVar4(f, "tz", 1, 0, 1);
  auto* tv = f.ctx.CreateVariable("zt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("zf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tz");
  ternary->true_expr = MakeId(f.arena, "zt");
  ternary->false_expr = MakeId(f.arena, "zf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

TEST(ConditionalAmbiguousCondition, XConditionWithEqualBranchesReturnsValue) {
  SimFixture f;

  MakeVar4(f, "tc", 1, 0, 1);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tc");
  ternary->true_expr = MakeInt(f.arena, 5);
  ternary->false_expr = MakeInt(f.arena, 5);
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(ConditionalAmbiguousCondition, XConditionCombinesDifferentBranchesBitwise) {
  SimFixture f;

  MakeVar4(f, "td", 1, 0, 1);
  auto* tv = f.ctx.CreateVariable("tt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("tf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "td");
  ternary->true_expr = MakeId(f.arena, "tt");
  ternary->false_expr = MakeId(f.arena, "tf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

TEST(ConditionalExpressionSim, TernaryTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd10 : 8'd20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(ConditionalExpressionSim, TernaryFalseBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 0 ? 8'd10 : 8'd20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(ConditionalExpressionSim, NestedTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? (0 ? 8'd1 : 8'd2) : 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// --- Moved from test_parser_clause_11_04_11_b.cpp ---

TEST(ConditionalOperatorEval, TrueConditionSelectsTrueExpression) {
  ExprFixture f;
  auto* expr = ParseExprFrom("1 ? 42 : 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

// --- Moved from test_simulator_clause_11_03_05.cpp ---

TEST(ShortCircuit, TernaryEvaluatesTrueBranchOnly) {
  SimFixture f;
  MakeVar(f, "c", 8, 1);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "c"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(ShortCircuit, TernaryEvaluatesFalseBranchOnly) {
  SimFixture f;
  MakeVar(f, "c", 8, 0);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "c"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(ShortCircuit, TernaryTrueCondSkipsFalseBranchSideEffect) {
  SimFixture f;
  MakeVar(f, "c", 8, 1);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "se", 8, 99);
  auto result = EvalExpr(
      MakeTernary(f.arena, MakeId(f.arena, "c"), MakeId(f.arena, "t"),
                  MakeAssignExpr(f.arena, "se", 42)),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 99u);
}

TEST(ShortCircuit, TernaryFalseCondSkipsTrueBranchSideEffect) {
  SimFixture f;
  MakeVar(f, "c", 8, 0);
  MakeVar(f, "se", 8, 99);
  MakeVar(f, "e", 8, 20);
  auto result = EvalExpr(
      MakeTernary(f.arena, MakeId(f.arena, "c"),
                  MakeAssignExpr(f.arena, "se", 42), MakeId(f.arena, "e")),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("se")->value.ToUint64(), 99u);
}

// --- Moved from test_simulator_clause_11.cpp ---

TEST(TernaryOperatorSim, TernaryVariableCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int cond;\n"
      "  int result;\n"
      "  initial begin\n"
      "    cond = 5;\n"
      "    result = cond ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryOperatorSim, TernaryComparisonMax) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 30;\n"
      "    b = 50;\n"
      "    result = (a > b) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 50u);
}

TEST(TernaryOperatorSim, TernaryEqualityCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, result;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    result = (a == 0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(TernaryOperatorSim, TernaryChainedPriorityEncoder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, a, b, c, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    c = 30;\n"
      "    result = (sel == 0) ? a : (sel == 1) ? b : c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(TernaryOperatorSim, TernaryContinuousAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b;\n"
      "  wire [7:0] y;\n"
      "  assign y = sel ? a : b;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'd55;\n"
      "    b = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.ToUint64(), 55u);
}

TEST(TernaryOperatorSim, TernaryBlockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, result;\n"
      "  initial begin\n"
      "    x = 3;\n"
      "    result = (x != 0) ? 100 : 200;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 100u);
}

TEST(TernaryOperatorSim, TernaryNonblockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result <= sel ? 8'd11 : 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 22u);
}

TEST(TernaryOperatorSim, TernaryBitwiseCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    result = (a & b) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TernaryOperatorSim, TernaryLogicalOrCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "    result = (a || b) ? 7 : 8;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(TernaryOperatorSim, TernaryConcatResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] hi, lo;\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    hi = 8'hAB;\n"
      "    lo = 8'hCD;\n"
      "    result = 1 ? {hi, lo} : 16'h0000;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(TernaryOperatorSim, TernaryFunctionCallBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function int double_it(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = sel ? double_it(5) : double_it(3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(TernaryOperatorSim, TernaryDifferentWidthOperands) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    narrow = 4'hF;\n"
      "    wide = 8'hAA;\n"
      "    result = 0 ? narrow : wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(TernaryOperatorSim, TernarySignedOperands) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = -5;\n"
      "    b = 10;\n"
      "    result = (a < 0) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  auto neg5_u32 = static_cast<uint32_t>(-5);
  EXPECT_EQ(var->value.ToUint64(), neg5_u32);
}

TEST(TernaryOperatorSim, TernaryAlwaysComb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'd33;\n"
      "    b = 8'd44;\n"
      "  end\n"
      "  always_comb begin\n"
      "    y = sel ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(TernaryOperatorSim, TernaryAsFunctionArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function int add_one(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = add_one(sel ? 10 : 20);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 21u);
}

TEST(TernaryOperatorSim, TernaryArithmeticBranches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, a, b, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 15;\n"
      "    b = 5;\n"
      "    result = sel ? (a + b) : (a - b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(TernaryOperatorSim, TernaryUnaryNotCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = !sel ? 77 : 88;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TernaryOperatorSim, TernaryMultipleInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    result = (a ? 10 : 20) + (b ? 30 : 40);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 50u);
}

TEST(TernaryOperatorSim, TernaryResultInComputation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = (sel ? 6 : 3) * 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryOperatorSim, TernaryBitSelectCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] flags;\n"
      "  int result;\n"
      "  initial begin\n"
      "    flags = 8'b0000_0100;\n"
      "    result = flags[2] ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(TernaryOperatorSim, TernaryPartSelectOperands) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    result = 1 ? data[15:8] : data[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(TernaryOperatorSim, TernaryResultWidth8Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h01;\n"
      "    result = 1 ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(TernaryOperatorSim, TernaryResultWidth32Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 1 ? 32'hDEAD_BEEF : 32'h0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(TernaryOperatorSim, TernaryNestedOuterFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0 ? (1 ? 10 : 20) : 30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(TernaryOperatorSim, TernaryChainedDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 5;\n"
      "    result = (sel == 0) ? 100 :\n"
      "             (sel == 1) ? 200 :\n"
      "             (sel == 2) ? 300 : 999;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 999u);
}

TEST(TernaryOperatorSim, TernaryLogicalAndCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 4;\n"
      "    result = (a && b) ? 55 : 66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// Ambiguous condition: both branches' side effects must execute.
TEST(ConditionalAmbiguousCondition, BothBranchSideEffectsExecute) {
  SimFixture f;
  MakeVar4(f, "cond", 1, 0, 1);  // x condition
  MakeVar(f, "se_t", 8, 99);
  MakeVar(f, "se_f", 8, 99);
  EvalExpr(
      MakeTernary(f.arena, MakeId(f.arena, "cond"),
                  MakeAssignExpr(f.arena, "se_t", 11),
                  MakeAssignExpr(f.arena, "se_f", 22)),
      f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se_t")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("se_f")->value.ToUint64(), 22u);
}

// Table 11-20: both branches all-zero → result is all-zero.
TEST(ConditionalAmbiguousCondition, AllZeroBranchesCombineToZero) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "t", 4, 0b0000);
  MakeVar(f, "e", 4, 0b0000);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// Table 11-20: both branches all-one → result is all-one.
TEST(ConditionalAmbiguousCondition, AllOneBranchesCombineToOne) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "t", 4, 0b1111);
  MakeVar(f, "e", 4, 0b1111);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b1111u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// Table 11-20: all bits differ → all result bits are x.
TEST(ConditionalAmbiguousCondition, AllDifferingBitsBecomeX) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "t", 4, 0b1010);
  MakeVar(f, "e", 4, 0b0101);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval & ~result.words[0].bval, 0u);
  EXPECT_EQ(result.words[0].bval, 0b1111u);
}

// Table 11-20: x bits in branch values propagate to result.
TEST(ConditionalAmbiguousCondition, XInBranchesPropagates) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  auto* tv = f.ctx.CreateVariable("t", 4);
  tv->value = MakeLogic4Vec(f.arena, 4);
  tv->value.words[0].aval = 0b1111;
  tv->value.words[0].bval = 0b0010;  // bit 1 is x
  MakeVar(f, "e", 4, 0b1111);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  // bit 1 was x in true branch → must be x in result
  EXPECT_NE(result.words[0].bval & 0b0010u, 0u);
}

// z condition with equal branches returns the value with no x bits.
TEST(ConditionalAmbiguousCondition, ZConditionEqualBranchesReturnsValue) {
  SimFixture f;
  MakeVar4(f, "zc", 1, 0, 1);  // z condition
  MakeVar(f, "t", 8, 42);
  MakeVar(f, "e", 8, 42);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "zc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// Ambiguous condition with different-width operands: result width is max.
TEST(ConditionalAmbiguousCondition, DifferentWidthBranchesCombinedToMaxWidth) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "narrow", 4, 0b1111);
  MakeVar(f, "wide", 8, 0b11110000);
  auto result = EvalExpr(
      MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "narrow"),
                  MakeId(f.arena, "wide")),
      f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

// Multi-bit condition with partial x bits triggers ambiguous path.
TEST(ConditionalAmbiguousCondition, MultiBitPartialXTriggersAmbiguous) {
  SimFixture f;
  auto* cv = f.ctx.CreateVariable("cond", 4);
  cv->value = MakeLogic4Vec(f.arena, 4);
  cv->value.words[0].aval = 0b0001;
  cv->value.words[0].bval = 0b0010;  // bit 1 is x, bit 0 is 1
  MakeVar(f, "t", 4, 0b1100);
  MakeVar(f, "e", 4, 0b1010);
  auto result = EvalExpr(
      MakeTernary(f.arena, MakeId(f.arena, "cond"), MakeId(f.arena, "t"),
                  MakeId(f.arena, "e")),
      f.ctx, f.arena);
  // Condition has x bit → ambiguous path → branches combined
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

// &&& in ternary condition: both conjuncts true → true branch.
TEST(TernaryOperatorSim, CondPredicateTripleAndBothTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 1;\n"
      "    result = (a &&& b) ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// &&& in ternary condition: first conjunct false → false branch.
TEST(TernaryOperatorSim, CondPredicateTripleAndFirstFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "    result = (a &&& b) ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// &&& in ternary condition: second conjunct false → false branch.
TEST(TernaryOperatorSim, CondPredicateTripleAndSecondFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    result = (a &&& b) ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
