#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MakeDecimalLiteral(Arena& arena, std::string_view text,
                                uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = text;
  e->int_val = val;
  return e;
}

static Expr* MakeUnbasedUnsizedLiteral(Arena& arena, std::string_view text) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kUnbasedUnsizedLiteral;
  e->text = text;
  return e;
}

namespace {

TEST(NumberElaboration, SimpleDecimalIsSigned) {
  SimFixture f;
  auto* lit = MakeDecimalLiteral(f.arena, "42", 42);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(NumberElaboration, UnbasedUnsizedOneBitSelfDetermined) {
  SimFixture f;
  auto* lit = MakeUnbasedUnsizedLiteral(f.arena, "'1");
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

}  // namespace
