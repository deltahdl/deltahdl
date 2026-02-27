// §7.4.5: Indexing and slicing of arrays

#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

namespace {

TEST(ArrayAccess, OutOfBoundsReturnsX) {
  SimFixture f;
  // Register a 4-element array arr[0:3], each element 8 bits.
  f.ctx.RegisterArray("arr", {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }
  // In-bounds: arr[2] should return 30.
  auto in_result = EvalExpr(MakeSelect(f.arena, "arr", 2), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 30u);
  EXPECT_TRUE(in_result.IsKnown());
  // Out-of-bounds: arr[10] should return X.
  auto oob_result = EvalExpr(MakeSelect(f.arena, "arr", 10), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

}  // namespace
