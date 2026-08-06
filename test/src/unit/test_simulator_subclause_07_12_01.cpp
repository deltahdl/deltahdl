#include <cstdint>
#include <string>
#include <utility>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array_locator.h"
#include "helpers_queue.h"
#include "helpers_scheduler.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MakeLocatorExpr(Arena& arena, std::string_view var,
                             std::string_view method, Expr* with_expr) {
  auto* call = MakeMethodCall(arena, var, method, {});
  call->with_expr = with_expr;
  return call;
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

// ===========================================================================
// End-to-end tests: the locator input is built from a dependency subclause's
// real declaration syntax and driven through the full pipeline (parse,
// elaborate, lower, run), then the queue/scalar result is read back — rather
// than hand-building the array and calling the locator helper directly.
// ===========================================================================

// §7.12.1 — find() returns every element satisfying the with expression.
// Built from a real dynamic-array (§7.5) `{...}` initializer, filtered with
// (item > 10) over {5,15,25,35}: three elements qualify, so the result queue's
// size() is 3.
TEST(ArrayLocator, FindOverDynamicArrayCountEndToEnd) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 15, 25, 35};\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    found = arr.find with (item > 10);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 3u);
}

// §7.12.1 — find_first() returns the leftmost element satisfying the with
// expression. Over the dynamic array {5,15,25,35} with (item > 10) the first
// qualifying element is 15, read back from the single-element result queue.
TEST(ArrayLocator, FindFirstOverDynamicArrayValueEndToEnd) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 15, 25, 35};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find_first with (item > 10);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 15u);
}

// §7.12.1 — index locator methods over a non-associative array return a queue
// of int holding 0-based positions. find_index for the element equal to 30 in
// {10,20,30} yields position 2.
TEST(ArrayLocator, FindIndexReturnsPositionEndToEnd) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {10, 20, 30};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_index with (item == 30);\n"
      "    p = idx[0];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

// §7.12.1 — when no element satisfies the with expression the returned queue is
// empty. Seeding sz to a nonzero value first proves the observed 0 comes from
// the empty result rather than a default.
TEST(ArrayLocator, FindNoMatchReturnsEmptyEndToEnd) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[] = {1, 2, 3};\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    sz = 99;\n"
      "    found = arr.find with (item > 100);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

// §7.12.1 — with the with clause omitted, min() selects the smallest element
// (as if with(item) were given). Over the dynamic array {50,10,30} the minimum
// is 10, returned as a scalar.
TEST(ArrayLocator, MinOverDynamicArrayEndToEnd) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  int arr[] = {50, 10, 30};\n"
      "  int r;\n"
      "  initial r = arr.min;\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 10u);
}

// §7.12.1 — locator methods operate on any unpacked array, including a
// fixed-size array (§7.4) built from an '{...} assignment pattern. max() over
// {10,50,30} returns 50.
TEST(ArrayLocator, MaxOverFixedArrayEndToEnd) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  logic [7:0] a [0:2] = '{ 8'd10, 8'd50, 8'd30 };\n"
      "  int r;\n"
      "  initial r = a.max;\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 50u);
}

// §7.12.1 — unique() returns one entry per distinct value. Built from a real
// queue (§7.10) {10,20,10,30,20}, three distinct values remain, so the result
// queue's size() is 3.
TEST(ArrayLocator, UniqueOverQueueEndToEnd) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int q [$] = {10, 20, 10, 30, 20};\n"
      "  int u [$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    u = q.unique;\n"
      "    sz = u.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 3u);
}

// §7.12.1 — a find() locator with a predicate driven over a real queue (§7.10).
// {5,15,25} with (item > 10) matches two elements.
TEST(ArrayLocator, FindOverQueueCountEndToEnd) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int q [$] = {5, 15, 25};\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    found = q.find with (item > 10);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 2u);
}

// §7.12.1 — for an associative array (§7.8) an index locator returns a queue of
// the index type holding the matching keys, not 0-based positions. With keys
// {10:5, 20:15, 30:25} and (item > 10), the matching keys are 20 and 30; the
// first (in ascending key order) is 20.
TEST(ArrayLocator, AssocFindIndexReturnsKeyEndToEnd) {
  uint64_t k = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int found[$];\n"
      "  int k;\n"
      "  initial begin\n"
      "    aa[10] = 5;\n"
      "    aa[20] = 15;\n"
      "    aa[30] = 25;\n"
      "    found = aa.find_index with (item > 10);\n"
      "    k = found[0];\n"
      "  end\n"
      "endmodule\n",
      "k");
  EXPECT_EQ(k, 20u);
}

// §7.12.1 — for an associative array, "first" is the entry with the smallest
// index (the §7.9 first() ordering), independent of insertion order. Inserting
// keys 30,10,20, find_first returns the value stored at the smallest key 10.
TEST(ArrayLocator, AssocFindFirstByKeyOrderEndToEnd) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[30] = 25;\n"
      "    aa[10] = 5;\n"
      "    aa[20] = 15;\n"
      "    found = aa.find_first with (item > 0);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 5u);
}

// §7.12.1 — likewise "last" is the entry with the largest index. find_last over
// the same associative array returns the value stored at the largest key 30.
TEST(ArrayLocator, AssocFindLastByKeyOrderEndToEnd) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[30] = 25;\n"
      "    aa[10] = 5;\n"
      "    aa[20] = 15;\n"
      "    found = aa.find_last with (item > 0);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 25u);
}

// §7.12.1 — when a with clause is present, unique() collapses on the value of
// that expression. {1,2,3,4} with (item % 2) keeps one element per parity, so
// the result queue's size() is 2.
TEST(ArrayLocator, UniqueGroupsByWithExpressionEndToEnd) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[] = {1, 2, 3, 4};\n"
      "  int u [$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    u = arr.unique with (item % 2);\n"
      "    sz = u.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 2u);
}

}  // namespace
