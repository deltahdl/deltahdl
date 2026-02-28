// §11.4.3: Arithmetic operators

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// ==========================================================================
// Power operator (**)
// ==========================================================================
TEST(EvalOp, PowerBasic) {
  SimFixture f;
  // 2 ** 10 = 1024
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeInt(f.arena, 10));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1024u);
}

TEST(EvalOp, PowerZeroExponent) {
  SimFixture f;
  // 5 ** 0 = 1
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, PowerOneExponent) {
  SimFixture f;
  // 7 ** 1 = 7
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 7),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

}  // namespace
