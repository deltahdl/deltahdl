#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

// Builds a fixed-size (non-dynamic) unpacked array as individual arr[i] element
// variables. map() reaches these through the non-queue element-collection path,
// distinct from MakeDynArray's queue backing.
void MakeFixedArray(SimFixture& f, std::string_view name,
                    const std::vector<uint64_t>& vals) {
  ArrayInfo info;
  info.lo = 0;
  info.size = static_cast<uint32_t>(vals.size());
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray(name, info);
  for (size_t i = 0; i < vals.size(); ++i) {
    auto elem = std::string(name) + "[" + std::to_string(i) + "]";
    auto* v = f.ctx.CreateVariable(elem, 32);
    v->value = MakeLogic4VecVal(f.arena, 32, vals[i]);
  }
}

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

// §7.12.5 — the with clause is required for map(): every element is replaced by
// the value of that expression, so a call lacking it is an error rather than a
// silent no-op.
TEST(ArrayMap, MapRequiresWithClause) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15});
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.12.5 — each returned element takes the self-determined type of the with
// expression, not the element type of the source array. A comparison yields a
// 1-bit value, so every mapped element is 1 bit wide even though the 32-bit
// source elements feed the expression.
TEST(ArrayMap, MapElementTypeIsWithExpressionType) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15});
  auto* with_expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                               MakeInt(f.arena, 5));
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].width, 1u);
  EXPECT_EQ(out[1].width, 1u);
  EXPECT_EQ(out[2].width, 1u);
  EXPECT_EQ(out[0].ToUint64(), 0u);
  EXPECT_EQ(out[1].ToUint64(), 1u);
  EXPECT_EQ(out[2].ToUint64(), 1u);
}

// §7.12.5 — edge case for the range-match rule: mapping an empty source yields
// an empty result (and is not an error, since the with clause is present). The
// returned array has the same, empty, range as the source.
TEST(ArrayMap, MapOnEmptyArrayReturnsEmpty) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  auto* with_expr =
      MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "item"),
                 MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out.size(), 0u);
}

// §7.12.5 — map() applies to any unpacked array, not only dynamic ones. A
// fixed-size source maps element-by-element through the non-queue collection
// path, and the result keeps the source's range: one element per source
// element, in position order.
TEST(ArrayMap, MapOnFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "fa", {3, 6, 9});
  auto* with_expr =
      MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "item"),
                 MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "fa", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 6u);
  EXPECT_EQ(out[1].ToUint64(), 12u);
  EXPECT_EQ(out[2].ToUint64(), 18u);
}

}
