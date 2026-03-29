#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MakeSizedLiteral(Arena& arena, std::string_view text,
                              uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = text;
  e->int_val = val;
  return e;
}

namespace {

// --- Signedness based on base specifier ---

TEST(IntegerLiteralElaboration, UnbasedDecimalIsSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "42", 42);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

TEST(IntegerLiteralElaboration, SignedBaseLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "4'sd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(IntegerLiteralElaboration, UnsignedBaseLiteralNotSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "4'd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(IntegerLiteralElaboration, SignedHexLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "8'shFF", 0xFF);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(IntegerLiteralElaboration, UnsizedBasedUnsignedIsNotSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "'d12", 12);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(IntegerLiteralElaboration, UnsizedBasedSignedIsSigned) {
  SimFixture f;
  auto* lit = MakeSizedLiteral(f.arena, "'sd12", 12);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

// --- Negation/division examples from §11.3.3 ---

TEST(IntegerLiteralElaboration, NegatedUnbasedDivThreeEqualsMinusFour) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

TEST(IntegerLiteralElaboration, NegatedUnsignedBasedDivThree) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-'d12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1431655761);
}

TEST(IntegerLiteralElaboration, NegatedSignedBasedDivThreeEqualsMinusFour) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-'sd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

TEST(IntegerLiteralElaboration, NegatedSizedSignedBasedDivThreeEqualsOne) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-4'sd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1);
}

}  // namespace
