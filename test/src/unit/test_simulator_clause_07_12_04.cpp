#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/eval_array.h"

using namespace delta;

static void MakeDynArray(SimFixture& f, std::string_view name,
                         const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = static_cast<uint32_t>(vals.size());
  f.ctx.RegisterArray(name, info);
}

namespace {

// §7.12.4: item.index in with-clause provides the element index.
TEST(ArrayIterator, ItemIndexInFindIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {100, 200, 300});
  // with (item.index > 0) — selects indices 1 and 2.
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

// §7.12.4: item.index used in find returns elements at matching indices.
TEST(ArrayIterator, ItemIndexInFind) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});
  // with (item.index < 2) — selects elements at indices 0 and 1.
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

}  // namespace
