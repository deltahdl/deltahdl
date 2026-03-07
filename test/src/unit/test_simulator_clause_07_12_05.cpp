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

// §7.12.5: map transforms each element via with-clause expression.
TEST(ArrayMap, MapDoubleElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15});
  // with (item + item) — doubles each element.
  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                                MakeId(f.arena, "item"),
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

// §7.12.5: map with item.index produces index-based result.
TEST(ArrayMap, MapWithIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {100, 200, 300});
  // with (item.index) — returns indices as values.
  auto* with_expr = MakeId(f.arena, "item.index");
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 0u);
  EXPECT_EQ(out[1].ToUint64(), 1u);
  EXPECT_EQ(out[2].ToUint64(), 2u);
}

}  // namespace
