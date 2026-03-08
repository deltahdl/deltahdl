#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalOp, LtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(EvalOp, GtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(EvalOpXZ, ReductionAndWithX) {
  SimFixture f;

  MakeVar4(f, "ra", 4, 0b1011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ra"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionAndWithKnown0) {
  SimFixture f;

  MakeVar4(f, "rb", 4, 0b0011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithKnown1) {
  SimFixture f;

  MakeVar4(f, "rc", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rc"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithX) {
  SimFixture f;

  MakeVar4(f, "rd", 4, 0b0000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXorWithX) {
  SimFixture f;

  MakeVar4(f, "re", 4, 0b1010, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "re"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SimA83, ReductionAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = &8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimA83, ReductionOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = |8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SimA86, UnaryReductionAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = &8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimA86, UnaryReductionNand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~&8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SimA86, UnaryReductionOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = |8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SimA86, UnaryReductionNor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~|8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimA86, UnaryReductionXor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ^8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SimA86, UnaryReductionXnor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~^8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimA86, UnaryReductionXnorAlt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ^~8'hA5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalOp, ReductionAndAllOnes) {
  SimFixture f;

  auto* expr =
      MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0xFFFFFFFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionAndNotAllOnes) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionOrNonZero) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionOrZero) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorEvenOnes) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorOddOnes) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNand) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNor) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorTildeCaret) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorCaretTilde) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kCaretTilde, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionAndZero) {
  SimFixture f;

  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
