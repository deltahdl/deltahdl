#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array_locator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/sim_context.h"

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
  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 1));
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
  auto* with_expr = MakeBinary(f.arena, TokenKind::kStar,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 2));
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

// §7.12.5 — for an associative source, map() returns an array with the same set
// of index values, each value replaced by the with expression. The keys carry
// over unchanged; only the stored values change.
TEST(ArrayMap, AssocMapPreservesKeysAndReplacesValues) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{10, 5}, {20, 15}, {30, 25}});
  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "aa", "map", {});
  call->with_expr = with_expr;
  AssocArrayObject out;
  bool ok = TryCollectAssocMapResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.int_data.size(), 3u);
  EXPECT_EQ(out.int_data.at(10).ToUint64(), 6u);
  EXPECT_EQ(out.int_data.at(20).ToUint64(), 16u);
  EXPECT_EQ(out.int_data.at(30).ToUint64(), 26u);
}

// §7.12.5 — the returned associative array's index type matches the source. A
// non-default 16-bit index type is preserved through the mapping.
TEST(ArrayMap, AssocMapPreservesIndexType) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{1, 100}, {2, 200}}, /*index_width=*/16);
  auto* with_expr = MakeBinary(f.arena, TokenKind::kStar,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "aa", "map", {});
  call->with_expr = with_expr;
  AssocArrayObject out;
  bool ok = TryCollectAssocMapResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.index_width, 16u);
  EXPECT_FALSE(out.is_string_key);
  ASSERT_EQ(out.int_data.size(), 2u);
  EXPECT_EQ(out.int_data.at(1).ToUint64(), 200u);
  EXPECT_EQ(out.int_data.at(2).ToUint64(), 400u);
}

// §7.12.5 — each mapped element of an associative source also takes the
// self-determined type of the with expression. A comparison yields 1-bit
// values, independent of the 32-bit source element width.
TEST(ArrayMap, AssocMapElementTypeIsWithExpressionType) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{0, 3}, {1, 8}});
  auto* with_expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                               MakeInt(f.arena, 5));
  auto* call = MakeMethodCall(f.arena, "aa", "map", {});
  call->with_expr = with_expr;
  AssocArrayObject out;
  bool ok = TryCollectAssocMapResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.int_data.size(), 2u);
  EXPECT_EQ(out.int_data.at(0).width, 1u);
  EXPECT_EQ(out.int_data.at(1).width, 1u);
  EXPECT_EQ(out.int_data.at(0).ToUint64(), 0u);
  EXPECT_EQ(out.int_data.at(1).ToUint64(), 1u);
}

// §7.12.5 — edge case of the index-values/range-match rule for an associative
// source: mapping an empty associative array yields an empty result (no error,
// since the with clause is present), and the empty set of index values matches
// the source.
TEST(ArrayMap, AssocMapOnEmptyArrayReturnsEmpty) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {}, /*index_width=*/16);
  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "aa", "map", {});
  call->with_expr = with_expr;
  AssocArrayObject out;
  bool ok = TryCollectAssocMapResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out.int_data.size(), 0u);
  EXPECT_EQ(out.index_width, 16u);
}

// §7.12.5 — the with clause is required for map() on an associative source just
// as for an indexed one; a bare call is an error.
TEST(ArrayMap, AssocMapRequiresWithClause) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{10, 5}});
  auto* call = MakeMethodCall(f.arena, "aa", "map", {});
  AssocArrayObject out;
  bool ok = TryCollectAssocMapResult(call, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
