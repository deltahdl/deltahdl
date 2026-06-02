#include <cstdint>
#include <string>
#include <utility>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MakeLocatorExpr(Arena& arena, std::string_view var,
                             std::string_view method, Expr* with_expr) {
  auto* call = MakeMethodCall(arena, var, method, {});
  call->with_expr = with_expr;
  return call;
}

// Builds a fixed-size (non-dynamic) unpacked array as individual element
// variables named arr[i] — the representation the locator's non-queue
// collection path reads from, distinct from MakeDynArray's queue backing.
static void MakeFixedArray(SimFixture& f, std::string_view name,
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

// Builds an integer-keyed associative array from (key, value) pairs. The keys
// need not be supplied in order; the underlying map keeps them sorted.
static void MakeIntAssoc(SimFixture& f, std::string_view name,
                         const std::vector<std::pair<int64_t, uint64_t>>& kv,
                         uint32_t index_width = 32) {
  auto* aa = f.ctx.CreateAssocArray(name, /*elem_width=*/32,
                                    /*is_string_key=*/false, index_width,
                                    /*is_wildcard=*/false, /*is_4state=*/false,
                                    /*is_index_signed=*/true);
  for (const auto& [k, v] : kv)
    aa->int_data[k] = MakeLogic4VecVal(f.arena, 32, v);
}

namespace {

TEST(ArrayLocator, UniqueReturnsDistinct) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 10, 30, 20});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 3u);
}

TEST(ArrayLocator, UniqueIndexReturnsFirstIndices) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 10, 30, 20});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique_index", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 0u);
  EXPECT_EQ(out[1].ToUint64(), 1u);
  EXPECT_EQ(out[2].ToUint64(), 3u);
}

TEST(ArrayLocator, FindWithPredicate) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25, 35});

  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 15u);
  EXPECT_EQ(out[1].ToUint64(), 25u);
  EXPECT_EQ(out[2].ToUint64(), 35u);
}

TEST(ArrayLocator, FindFirstReturnsSingleMatch) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_first", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 15u);
}

TEST(ArrayLocator, FindLastReturnsLastMatch) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_last", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 25u);
}

TEST(ArrayLocator, FindIndexReturnsMatchingIndices) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25, 35});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
  EXPECT_EQ(out[1].ToUint64(), 2u);
  EXPECT_EQ(out[2].ToUint64(), 3u);
}

TEST(ArrayLocator, FindLastIndexReturnsLastMatchIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25, 35});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_last_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 3u);
}

TEST(ArrayLocator, FindNoMatchReturnsEmpty) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 100));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 0u);
}

TEST(ArrayLocator, FindFirstIndexReturnsFirstMatchIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25, 35});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_first_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
}

TEST(ArrayLocator, FindOnEmptyArrayReturnsEmpty) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 0));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 0u);
}

TEST(ArrayLocator, UniqueOnEmptyArrayReturnsEmpty) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 0u);
}

TEST(ArrayLocator, MinWithDuplicatesReturnsSingleElement) {
  SimFixture f;
  MakeDynArray(f, "d", {10, 10, 20});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "min", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 10u);
}

TEST(ArrayLocator, MaxWithDuplicatesReturnsSingleElement) {
  SimFixture f;
  MakeDynArray(f, "d", {20, 20, 10});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "max", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 20u);
}

TEST(ArrayLocator, UniqueReturnsOnePerValue) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 5, 5, 5});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 5u);
}

TEST(ArrayLocator, UniqueIndexReturnsOnePerValue) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 5, 5});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique_index", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 1u);
}

TEST(ArrayLocator, FindIndexReturnsIntType) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 20));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].width, 32u);
}

TEST(ArrayLocator, FindLastIndexReturnsIntType) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 20));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_last_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].width, 32u);
}

TEST(ArrayLocator, UniqueIndexReturnsIntType) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 10});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique_index", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_GE(out.size(), 1u);
  EXPECT_EQ(out[0].width, 32u);
}

TEST(ArrayLocator, MinReturnsSmallest) {
  SimFixture f;
  MakeDynArray(f, "d", {50, 10, 30});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "min", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 10u);
}

TEST(ArrayLocator, MaxReturnsLargest) {
  SimFixture f;
  MakeDynArray(f, "d", {50, 10, 30});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "max", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 50u);
}

// §7.12.1 — the with clause is mandatory for the find* locators.
TEST(ArrayLocator, FindWithoutWithIsError) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25});
  auto* expr = MakeMethodCall(f.arena, "arr", "find", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ArrayLocator, FindIndexWithoutWithIsError) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25});
  auto* expr = MakeMethodCall(f.arena, "arr", "find_first_index", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.12.1 — by contrast, min/max/unique/unique_index accept an omitted with
// clause (the predicate defaults to the element value itself).
TEST(ArrayLocator, UniqueWithoutWithIsNotError) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 5, 9});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_TRUE(ok);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.12.1 — min()/max() return the element whose with expression is extreme,
// which is not necessarily the element with the extreme value. For {3, 1, 2}
// with (5 - item) the expression values are {2, 4, 3}: the minimum expression
// (2) belongs to element value 3 and the maximum (4) to element value 1.
TEST(ArrayLocator, MinUsesWithExpressionNotElementValue) {
  SimFixture f;
  MakeDynArray(f, "arr", {3, 1, 2});
  auto* pred = MakeBinary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 5),
                          MakeId(f.arena, "item"));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "min", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 3u);
}

TEST(ArrayLocator, MaxUsesWithExpressionNotElementValue) {
  SimFixture f;
  MakeDynArray(f, "arr", {3, 1, 2});
  auto* pred = MakeBinary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 5),
                          MakeId(f.arena, "item"));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "max", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
}

// §7.12.1 — unique()/unique_index() collapse on the with expression value, so
// {1, 2, 3, 4} with (item % 2) keeps one entry per parity: the first odd
// element (value 1, index 0) and the first even element (value 2, index 1).
TEST(ArrayLocator, UniqueGroupsByWithExpression) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3, 4});
  auto* pred = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 2));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "unique", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
  EXPECT_EQ(out[1].ToUint64(), 2u);
}

TEST(ArrayLocator, UniqueIndexGroupsByWithExpression) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3, 4});
  auto* pred = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 2));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "unique_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 0u);
  EXPECT_EQ(out[1].ToUint64(), 1u);
}

// §7.12.1 — locator methods operate on any unpacked array, not only dynamic
// ones. A fixed-size array {7, 3, 9, 1} filtered with (item > 4) yields its
// two matching elements, exercising the non-queue element-collection path.
TEST(ArrayLocator, FindOnFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "fa", {7, 3, 9, 1});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 4));
  auto* expr = MakeLocatorExpr(f.arena, "fa", "find", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 7u);
  EXPECT_EQ(out[1].ToUint64(), 9u);
}

// §7.12.1 — an omitted with clause behaves as if with(item) were given: the
// expression value is the element itself, so both forms select the same min.
TEST(ArrayLocator, OmittedWithEquivalentToWithItem) {
  SimFixture f;
  MakeDynArray(f, "arr", {50, 10, 30});
  auto* implicit_expr = MakeMethodCall(f.arena, "arr", "min", {});
  std::vector<Logic4Vec> implicit_out;
  ASSERT_TRUE(
      TryCollectLocatorResult(implicit_expr, f.ctx, f.arena, implicit_out));
  auto* explicit_expr =
      MakeLocatorExpr(f.arena, "arr", "min", MakeId(f.arena, "item"));
  std::vector<Logic4Vec> explicit_out;
  ASSERT_TRUE(
      TryCollectLocatorResult(explicit_expr, f.ctx, f.arena, explicit_out));
  ASSERT_EQ(implicit_out.size(), 1u);
  ASSERT_EQ(explicit_out.size(), 1u);
  EXPECT_EQ(implicit_out[0].ToUint64(), explicit_out[0].ToUint64());
  EXPECT_EQ(implicit_out[0].ToUint64(), 10u);
}

// §7.12.1 — index locators on an associative array return the matching keys
// (the index type), not 0-based positions, and in ascending key order. Keys
// {10:5, 20:15, 30:25} with (item > 10) match keys 20 and 30.
TEST(ArrayLocator, AssocFindIndexReturnsKeys) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{10, 5}, {20, 15}, {30, 25}});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 10));
  auto* expr = MakeLocatorExpr(f.arena, "aa", "find_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 20u);
  EXPECT_EQ(out[1].ToUint64(), 30u);
}

// §7.12.1 — the returned index values carry the associative index type, so a
// 16-bit index domain yields 16-bit results rather than int's 32 bits.
TEST(ArrayLocator, AssocFindIndexReturnsIndexTypeWidth) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{1, 100}, {2, 200}}, /*index_width=*/16);
  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 200));
  auto* expr = MakeLocatorExpr(f.arena, "aa", "find_index", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 2u);
  EXPECT_EQ(out[0].width, 16u);
}

// §7.12.1 — for an associative array, first/last are the smallest/largest
// index entries (the 7.9 ordering), independent of insertion order. find_first
// returns the value at key 10, find_last the value at key 30.
TEST(ArrayLocator, AssocFindFirstAndLastByKeyOrder) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{30, 25}, {10, 5}, {20, 15}});
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 0));
  auto* first = MakeLocatorExpr(f.arena, "aa", "find_first", pred);
  std::vector<Logic4Vec> fo;
  ASSERT_TRUE(TryCollectLocatorResult(first, f.ctx, f.arena, fo));
  ASSERT_EQ(fo.size(), 1u);
  EXPECT_EQ(fo[0].ToUint64(), 5u);
  auto* last = MakeLocatorExpr(f.arena, "aa", "find_last", pred);
  std::vector<Logic4Vec> lo;
  ASSERT_TRUE(TryCollectLocatorResult(last, f.ctx, f.arena, lo));
  ASSERT_EQ(lo.size(), 1u);
  EXPECT_EQ(lo[0].ToUint64(), 25u);
}

}
