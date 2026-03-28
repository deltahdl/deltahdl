#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(ArrayMap, MapDoubleElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15});

  auto* with_expr =
      MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "item"),
                 MakeId(f.arena, "item"));
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 10u);
  EXPECT_EQ(out[1].ToUint64(), 20u);
  EXPECT_EQ(out[2].ToUint64(), 30u);
}

}  // namespace
