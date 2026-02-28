// §11.4.5: Equality operators

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "simulator/eval.h"
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

TEST(ArrayEquality, UnequalArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  // Modify b[2] to differ.
  auto* v = f.ctx.FindVariable("b[2]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 99);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
