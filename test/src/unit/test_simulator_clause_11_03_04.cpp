#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StateOps, TwoStatePlusTwoState) {
  SimFixture f;
  MakeVar(f, "a", 8, 3);
  MakeVar(f, "b", 8, 5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(StateOps, TwoStateDivByZeroProducesX) {
  SimFixture f;
  MakeVar(f, "a", 8, 10);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kSlash,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(StateOps, ModByZeroProducesX) {
  SimFixture f;
  MakeVar(f, "a", 8, 10);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPercent,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

}  // namespace
