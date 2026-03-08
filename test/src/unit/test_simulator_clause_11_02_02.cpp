#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "simulator/evaluation.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(ArrayEquality, EqualArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
