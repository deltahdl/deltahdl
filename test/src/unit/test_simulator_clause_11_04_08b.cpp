// §11.4.8: Bitwise operators

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

namespace {

// ==========================================================================
// Reduction operators (unary &, |, ^, ~&, ~|, ~^, ^~)
// ==========================================================================
TEST(EvalOp, ReductionAndAllOnes) {
  SimFixture f;
  // &32'hFFFFFFFF = 1 (all 32 bits are 1)
  auto* expr =
      MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0xFFFFFFFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionAndNotAllOnes) {
  SimFixture f;
  // &32'd5 = 0 (not all bits 1)
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionOrNonZero) {
  SimFixture f;
  // |32'd4 = 1
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionOrZero) {
  SimFixture f;
  // |32'd0 = 0
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorEvenOnes) {
  SimFixture f;
  // ^32'd3 = 0 (two 1-bits => even parity)
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorOddOnes) {
  SimFixture f;
  // ^32'd7 = 1 (three 1-bits => odd parity)
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNand) {
  SimFixture f;
  // ~&32'd5 = 1 (not all bits 1)
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNor) {
  SimFixture f;
  // ~|32'd0 = 1
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorTildeCaret) {
  SimFixture f;
  // ~^32'd3 = 1 (even parity -> XNOR=1)
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorCaretTilde) {
  SimFixture f;
  // ^~32'd7 = 0 (odd parity -> XNOR=0)
  auto* expr = MakeUnary(f.arena, TokenKind::kCaretTilde, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ==========================================================================
// Additional edge cases
// ==========================================================================
TEST(EvalOp, ReductionAndZero) {
  SimFixture f;
  // &32'd0 = 0
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
