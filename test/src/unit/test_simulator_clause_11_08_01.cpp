#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §11.8.1: Decimal numbers are signed.
TEST(ExprType, DecimalLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 42);
  lit->text = "42";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_TRUE(result.is_signed);
}

// §11.8.1: Based numbers are unsigned (no 's' specifier).
TEST(ExprType, BasedLiteralIsUnsigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 0xA);
  lit->text = "8'hA";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xAu);
  EXPECT_FALSE(result.is_signed);
}

// §11.8.1: Based numbers with 's' specifier are signed.
TEST(ExprType, SignedBasedLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 0xA);
  lit->text = "4'shA";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

// §11.8.1: If any operand is unsigned, result is unsigned.
TEST(ExprType, MixedSignednessYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 5);
  MakeVar(f, "u", 8, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "s"), MakeId(f.arena, "u")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
  EXPECT_FALSE(result.is_signed);
}

// §11.8.1: If all operands are signed, result is signed.
TEST(ExprType, AllSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 5);
  MakeSignedVarAdv(f, "b", 8, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
  EXPECT_TRUE(result.is_signed);
}

// §11.8.1: Bit-select results are unsigned regardless of operand.
TEST(ExprType, BitSelectAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sv", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "sv");
  sel->index = MakeInt(f.arena, 7);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

// §11.8.1: Concatenation results are unsigned regardless of operands.
TEST(ExprType, ConcatAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "x", 4, 0xF);
  MakeSignedVarAdv(f, "y", 4, 0xA);
  auto* cat = f.arena.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->elements.push_back(MakeId(f.arena, "x"));
  cat->elements.push_back(MakeId(f.arena, "y"));
  auto result = EvalExpr(cat, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

// §11.8.1: Comparison results are unsigned.
TEST(ExprType, ComparisonAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "p", 8, 10);
  MakeSignedVarAdv(f, "q", 8, 20);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kGt,
                                    MakeId(f.arena, "p"), MakeId(f.arena, "q")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

// §11.8.1: Reduction operator results are unsigned.
TEST(ExprType, ReductionAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "r", 8, 0xFF);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "r")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

}  // namespace
