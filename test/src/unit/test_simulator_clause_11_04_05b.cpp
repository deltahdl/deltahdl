// §11.4.5: Equality operators

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

namespace {

// ==========================================================================
// Wildcard equality (==?, !=?)
// ==========================================================================
TEST(EvalOp, WildcardEqMatch) {
  SimFixture f;
  // 5 ==? 5 = 1 (no X/Z bits, exact match)
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, WildcardEqMismatch) {
  SimFixture f;
  // 5 ==? 3 = 0
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, WildcardNeqMatch) {
  SimFixture f;
  // 5 !=? 3 = 1
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, WildcardNeqSame) {
  SimFixture f;
  // 5 !=? 5 = 0
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
