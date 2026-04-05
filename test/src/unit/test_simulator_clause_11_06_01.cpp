#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ExpressionBitLength, WidthPropFromContext) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("wa", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0xF);
  auto* vb = f.ctx.CreateVariable("wb", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "wa"),
                          MakeId(f.arena, "wb"));

  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);

  auto r2 = EvalExpr(expr, f.ctx, f.arena, 8);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
  EXPECT_EQ(r2.width, 8u);
}

TEST(ExpressionBitLength, TernaryWidthFromBranches) {
  SimFixture f;

  auto* cond = f.ctx.CreateVariable("tc", 1);
  cond->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* tv = f.ctx.CreateVariable("tv", 8);
  tv->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* fv = f.ctx.CreateVariable("fv", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);

  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(ExpressionBitLength, AssignmentContextWidthPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(ExpressionBitLength, AssignmentContextWidthSameSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumA = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumA");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

TEST(ExpressionBitLength, ContextWidthPropagatesForMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a * a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xE1u);
}

TEST(ExpressionBitLength, CastingSetsContextWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

TEST(ExpressionBitLength, CastWidensIntermediateValue) {
  SimFixture f;
  MakeVar(f, "x", 4, 0xF);

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "x");

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
}

TEST(ExpressionBitLength, CastWidensOperandPreservesCarry) {
  SimFixture f;
  MakeVar(f, "a", 4, 0xF);
  MakeVar(f, "b", 4, 1);

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "a");

  auto* add = MakeBinary(f.arena, TokenKind::kPlus, cast, MakeId(f.arena, "b"));

  auto result = EvalExpr(add, f.ctx, f.arena);
  // int'(a) is 32-bit, so addition uses max(32, 4) = 32 bits.
  // 0xF + 0x1 = 0x10, carry preserved.
  EXPECT_EQ(result.ToUint64(), 0x10u);
  EXPECT_EQ(result.width, 32u);
}

TEST(ExpressionBitLength, SubtractionContextWidthPreservesBorrow) {
  SimFixture f;

  MakeVar(f, "sa", 8, 0);
  MakeVar(f, "sb", 8, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));

  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0xFFu);
  EXPECT_EQ(r1.width, 8u);

  auto r2 = EvalExpr(expr, f.ctx, f.arena, 16);
  EXPECT_EQ(r2.ToUint64(), 0xFFFFu);
  EXPECT_EQ(r2.width, 16u);
}

// Table 11-21: >> << >>> <<< → width of LHS, shift amount is self-determined.
TEST(ExpressionBitLength, ShiftWidthIsLhsWidth) {
  SimFixture f;
  MakeVar(f, "sv", 8, 0xFF);
  MakeVar(f, "sh", 16, 2);

  for (TokenKind op :
       {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
        TokenKind::kGtGtGt}) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "sv"), MakeId(f.arena, "sh"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 8u);
  }
}

// Table 11-21: ** → width of base (LHS).
TEST(ExpressionBitLength, PowerWidthIsBaseWidth) {
  SimFixture f;
  MakeVar(f, "base", 8, 3);
  MakeVar(f, "exp", 16, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeId(f.arena, "base"),
                          MakeId(f.arena, "exp"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 9u);
}

// Table 11-21: reduction ops → 1-bit result at runtime.
TEST(ExpressionBitLength, ReductionOpsProduceOneBit) {
  SimFixture f;
  MakeVar(f, "rv", 8, 0xFF);

  for (TokenKind op :
       {TokenKind::kAmp, TokenKind::kTildeAmp, TokenKind::kPipe,
        TokenKind::kTildePipe, TokenKind::kCaret, TokenKind::kTildeCaret,
        TokenKind::kCaretTilde}) {
    auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "rv"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 1u);
  }
}

// Table 11-21: ! → 1-bit result.
TEST(ExpressionBitLength, LogicalNotProducesOneBit) {
  SimFixture f;
  MakeVar(f, "nv", 16, 0);
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "nv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// Table 11-21: && || → 1-bit result, operands self-determined.
TEST(ExpressionBitLength, LogicalAndOrProduceOneBit) {
  SimFixture f;
  MakeVar(f, "la", 16, 1);
  MakeVar(f, "lb", 8, 1);

  auto* and_expr = MakeBinary(f.arena, TokenKind::kAmpAmp,
                              MakeId(f.arena, "la"), MakeId(f.arena, "lb"));
  auto r1 = EvalExpr(and_expr, f.ctx, f.arena);
  EXPECT_EQ(r1.width, 1u);

  auto* or_expr = MakeBinary(f.arena, TokenKind::kPipePipe,
                             MakeId(f.arena, "la"), MakeId(f.arena, "lb"));
  auto r2 = EvalExpr(or_expr, f.ctx, f.arena);
  EXPECT_EQ(r2.width, 1u);
}

// Table 11-21: -> <-> → 1-bit result, operands self-determined.
TEST(ExpressionBitLength, ImplicationAndEquivalenceProduceOneBit) {
  SimFixture f;
  MakeVar(f, "ia", 16, 1);
  MakeVar(f, "ib", 8, 0);

  auto* impl = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ia"),
                           MakeId(f.arena, "ib"));
  auto r1 = EvalExpr(impl, f.ctx, f.arena);
  EXPECT_EQ(r1.width, 1u);
  EXPECT_EQ(r1.ToUint64(), 0u);

  auto* equiv = MakeBinary(f.arena, TokenKind::kLtDashGt,
                           MakeId(f.arena, "ia"), MakeId(f.arena, "ib"));
  auto r2 = EvalExpr(equiv, f.ctx, f.arena);
  EXPECT_EQ(r2.width, 1u);
  EXPECT_EQ(r2.ToUint64(), 0u);
}

// Table 11-21: comparison ops → 1-bit result at runtime.
TEST(ExpressionBitLength, ComparisonOpsProduceOneBit) {
  SimFixture f;
  MakeVar(f, "ca", 16, 5);
  MakeVar(f, "cb", 8, 5);

  for (TokenKind op :
       {TokenKind::kEqEq, TokenKind::kBangEq, TokenKind::kEqEqEq,
        TokenKind::kBangEqEq, TokenKind::kLt, TokenKind::kGt,
        TokenKind::kLtEq, TokenKind::kGtEq}) {
    auto* expr = MakeBinary(f.arena, op, MakeId(f.arena, "ca"),
                            MakeId(f.arena, "cb"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 1u);
  }
}

// Self-determined: shift amount does not affect result width.
TEST(ExpressionBitLength, ShiftAmountIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "sd", 4, 0x8);
  MakeVar(f, "sa", 32, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 4u);
}

// Self-determined: ternary condition does not affect branch width.
TEST(ExpressionBitLength, TernaryConditionIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "tc32", 32, 1);
  MakeVar(f, "ttv", 4, 0xA);
  MakeVar(f, "tfv", 4, 0x5);

  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc32");
  tern->true_expr = MakeId(f.arena, "ttv");
  tern->false_expr = MakeId(f.arena, "tfv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
}

// Replication width at runtime: {3{8'hFF}} → 24 bits.
TEST(ExpressionBitLength, ReplicationWidthIsCountTimesElement) {
  SimFixture f;
  MakeVar(f, "re", 8, 0xFF);
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 3);
  repl->elements.push_back(MakeId(f.arena, "re"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
}

// Context-determined: division with wider LHS target.
TEST(ExpressionBitLength, DivisionContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a / 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
  EXPECT_EQ(var->value.width, 8u);
}

// Context-determined: modulus with wider LHS target.
TEST(ExpressionBitLength, ModulusContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a % 4'hB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
  EXPECT_EQ(var->value.width, 8u);
}

// Context-determined: bitwise AND with wider LHS target.
TEST(ExpressionBitLength, BitwiseAndContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 4'hA;\n"
      "    result = a & b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
  EXPECT_EQ(var->value.width, 8u);
}

}  // namespace
