#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(ArrayIterator, ItemIndexInFindIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {100, 200, 300});

  auto* pred = MakeBinary(f.arena, TokenKind::kGt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 0));
  auto* call = MakeMethodCall(f.arena, "arr", "find_index", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
  EXPECT_EQ(out[1].ToUint64(), 2u);
}

TEST(ArrayIterator, ItemIndexInFind) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});

  auto* pred = MakeBinary(f.arena, TokenKind::kLt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 10u);
  EXPECT_EQ(out[1].ToUint64(), 20u);
}

}
