#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalOpXZ, WildcardEqLeftX) {
  SimFixture f;

  MakeVar4(f, "wl", 4, 0b0001, 0b1000);
  auto* b = f.ctx.CreateVariable("wr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0001);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "wl"), MakeId(f.arena, "wr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(OperatorSim, BinaryWildcardEq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
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

TEST(OperatorSim, BinaryWildcardNeq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
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

TEST(EvalOp, WildcardEqMatch) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, WildcardEqMismatch) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, WildcardNeqMatch) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, WildcardNeqSame) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, WildcardEqRhsXWildcardMatch) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b0111, 0b0000);

  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, WildcardEqNonWildcardBitsDiffer) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b1111, 0b0000);

  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, WildcardEqLhsXMaskedByRhsWildcard) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b0101, 0b0010);

  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, WildcardNeqLeftXReturnsX) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b0001, 0b1000);

  auto* b = f.ctx.CreateVariable("b", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0001);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, WildcardNeqRhsWildcardDifferent) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b1101, 0b0000);

  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, WildcardNeqRhsWildcardMatch) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b0111, 0b0000);

  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, WildcardEqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, WildcardNeqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(OperatorSim, WildcardEqWithXLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b0101 ==? 4'b01x1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalOpXZ, WildcardEqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;

  // The wildcard (right) operand is narrower than the left operand. §11.4.6
  // requires it to be extended the same way as for logical equality, i.e.
  // zero-extended for unsigned values. The extended high bits are plain zeros,
  // not wildcards, so a set high bit on the left makes the comparison fail.
  MakeVar4(f, "wide", 8, 0b00010101, 0b00000000);

  MakeVar4(f, "narrow", 4, 0b0101, 0b0000);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "wide"), MakeId(f.arena, "narrow"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, WildcardEqUnequalWidthMatchesAfterExtension) {
  SimFixture f;

  // With the left operand's high bits clear, the zero-extended narrow operand
  // matches across the full width and the relation holds.
  MakeVar4(f, "wide", 8, 0b00000101, 0b00000000);

  MakeVar4(f, "narrow", 4, 0b0101, 0b0000);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "wide"), MakeId(f.arena, "narrow"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, WildcardNeqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;

  // §11.4.6 extends operands of unequal length as for logical inequality. The
  // narrow right operand is zero-extended, so the left operand's set high bit
  // makes the operands differ and !=? reports true.
  MakeVar4(f, "wide", 8, 0b00010101, 0b00000000);

  MakeVar4(f, "narrow", 4, 0b0101, 0b0000);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "wide"), MakeId(f.arena, "narrow"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardNeqWithXLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b1101 !=? 4'b01x1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
