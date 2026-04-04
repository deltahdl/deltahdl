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

// RHS x bits act as wildcards: non-wildcard bits match → 1'b1.
TEST(EvalOpXZ, WildcardEqRhsXWildcardMatch) {
  SimFixture f;

  // LHS: 4'b0111  (aval=0b0111, bval=0)
  MakeVar4(f, "a", 4, 0b0111, 0b0000);
  // RHS: 4'b01x1  (bit 1 is x/wildcard)
  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// RHS z bits also act as wildcards.
TEST(EvalOpXZ, WildcardEqRhsZWildcardMatch) {
  SimFixture f;

  // LHS: 4'b0111
  MakeVar4(f, "a", 4, 0b0111, 0b0000);
  // RHS: 4'b01z1  (bit 1 is z/wildcard: aval=1,bval=1)
  MakeVar4(f, "b", 4, 0b0111, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// Non-wildcard bits differ → 1'b0.
TEST(EvalOpXZ, WildcardEqNonWildcardBitsDiffer) {
  SimFixture f;

  // LHS: 4'b1111
  MakeVar4(f, "a", 4, 0b1111, 0b0000);
  // RHS: 4'b01x1  (bit 1 is wildcard, but bit 3 differs)
  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// LHS x masked by RHS wildcard at same position → known result.
TEST(EvalOpXZ, WildcardEqLhsXMaskedByRhsWildcard) {
  SimFixture f;

  // LHS: bit 1 is x, others are known 0101
  MakeVar4(f, "a", 4, 0b0101, 0b0010);
  // RHS: bit 1 is also x (wildcard), others are 0101
  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // LHS x at bit 1 is masked by RHS wildcard → result is known.
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// !=? with LHS x in non-wildcard position → 1'bx.
TEST(EvalOpXZ, WildcardNeqLeftXReturnsX) {
  SimFixture f;

  // LHS: bit 3 is x
  MakeVar4(f, "a", 4, 0b0001, 0b1000);
  // RHS: all known
  auto* b = f.ctx.CreateVariable("b", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0001);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// !=? with RHS wildcard, non-wildcard bits differ → 1'b1.
TEST(EvalOpXZ, WildcardNeqRhsWildcardDifferent) {
  SimFixture f;

  // LHS: 4'b1101
  MakeVar4(f, "a", 4, 0b1101, 0b0000);
  // RHS: 4'b01x1  (bit 1 wildcard, bit 3 differs)
  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// !=? with RHS wildcard, all non-wildcard bits match → 1'b0.
TEST(EvalOpXZ, WildcardNeqRhsWildcardMatch) {
  SimFixture f;

  // LHS: 4'b0111
  MakeVar4(f, "a", 4, 0b0111, 0b0000);
  // RHS: 4'b01x1  (bit 1 wildcard, non-wildcard bits match)
  MakeVar4(f, "b", 4, 0b0101, 0b0010);

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].bval, 0u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Result is 1-bit self-determined.
TEST(EvalOp, WildcardEqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// !=? result is also 1-bit.
TEST(EvalOp, WildcardNeqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

// Full simulation: RHS x literal acts as wildcard.
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

// Full simulation: !=? with RHS x wildcard and differing non-wildcard bits.
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
