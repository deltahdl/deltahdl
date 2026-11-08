#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_array_locator.h"
#include "helpers_queue.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
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

TEST(ArrayLocator, FindWithoutWithIsError) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25});
  auto* expr = MakeMethodCall(f.arena, "arr", "find", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array locator method 'find' requires a 'with' clause", 0, "7.12.1"));
}

TEST(ArrayLocator, FindIndexWithoutWithIsError) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25});
  auto* expr = MakeMethodCall(f.arena, "arr", "find_first_index", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array locator method 'find_first_index' requires "
                            "a 'with' clause",
                            0, "7.12.1"));
}

TEST(ArrayLocator, UniqueWithoutWithIsNotError) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 5, 9});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_TRUE(ok);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

TEST(ArrayLocator, AssocFindIndexReturnsIndexTypeWidth) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{1, 100}, {2, 200}}, 16);
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

TEST(ArrayLocator, IndexedFindWithoutWithNames7_12_1) {
  SimFixture f;
  MakeDynArray(f, "arr", {2, 4, 6});
  auto* expr = MakeMethodCall(f.arena, "arr", "find_last", {});
  std::vector<Logic4Vec> out;
  TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "requires a 'with' clause", 0,
                            "7.12.1"));
}

TEST(ArrayLocator, AssocFindWithoutWithNames7_12_1) {
  SimFixture f;
  MakeIntAssoc(f, "aa", {{4, 40}, {5, 50}});
  auto* expr = MakeMethodCall(f.arena, "aa", "find_first", {});
  std::vector<Logic4Vec> out;
  TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "requires a 'with' clause", 0,
                            "7.12.1"));
}

TEST(ArrayLocator, StringItemComparesLexicographicallyInWith) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string SA[6] = '{\"Bob\", \"Henry\", \"abc\", \"Bob\", \"zed\", "
      "\"Al\"};\n"
      "  string a = \"Al\";\n"
      "  int qi[$];\n"
      "  initial begin\n"
      "    qi = SA.find_index with (item > \"Z\");\n"
      "    $display(\"%0d %0d %0d\", qi.size(), qi[0], qi[1]);\n"
      "    qi = SA.find_last_index(s) with (s > \"Z\");\n"
      "    $display(\"%0d %0d\", qi.size(), qi[0]);\n"
      "    qi = SA.find_index with (item < \"Z\");\n"
      "    $display(\"%0d\", qi.size());\n"
      "    $display(\"%0d\", a > \"Z\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 4\n1 4\n4\n0\n");
}

TEST(ArrayLocator, WithClauseCallsAStringMethodWithoutParentheses) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string SA[4] = '{\"7\", \"100\", \"42\", \"9\"};\n"
      "  string SB[5] = '{\"a\", \"A\", \"b\", \"a\", \"B\"};\n"
      "  string qs[$], qt[$], s = \"42\";\n"
      "  initial begin\n"
      "    qs = SA.max with (item.atoi);\n"
      "    qt = SB.unique(v) with (v.tolower);\n"
      "    $display(\"%0s %0d %0d %0d\", qs[0], qt.size(), s.atoi,\n"
      "             SA[1].atoi);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "100 2 42 100\n");
}

TEST(ArrayLocator, LocatorsOnAStringKeyedAssociativeArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int m[string];\n"
      "  string ks[$], kl[$]; int vs[$], vf[$];\n"
      "  initial begin\n"
      "    m[\"pear\"] = 7; m[\"apple\"] = 5; m[\"fig\"] = 2;\n"
      "    ks = m.find_index with (item > 3);\n"
      "    kl = m.find_last_index with (item > 3);\n"
      "    vs = m.find with (item > 3);\n"
      "    vf = m.find_first with (item.index != \"apple\");\n"
      "    $display(\"%0d %0s %0s %0s %0d %0d %0d\", ks.size(), ks[0], ks[1],\n"
      "             kl[0], vs.size(), vs[0], vf[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 apple pear pear 2 5 2\n");
}

TEST(ArrayLocator, MinAndMaxOrderTheElementsByTheElementTypesSignedness) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int d[] = '{5, -3};\n"
      "  int f[2] = '{5, -3};\n"
      "  int q[$] = '{5, -3};\n"
      "  bit [31:0] u[$] = '{-3, 5};\n"
      "  int aa[int];\n"
      "  int r1[$], r2[$], r3[$], r4[$], r5[$];\n"
      "  int s1, s2;\n"
      "  initial begin\n"
      "    aa[0] = 5; aa[1] = -3;\n"
      "    s1 = d.min; s2 = f.max;\n"
      "    r1 = q.min; r2 = q.max; r3 = aa.min; r4 = aa.max; r5 = u.min;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", s1, s2, r1[0], r2[0],\n"
      "             r3[0], r4[0], r5[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 5 -3 5 -3 5 5\n");
}

TEST(ArrayLocator, MinAndMaxWithAClauseOrderByTheClausesSignedness) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int q[$] = '{5, -3};\n"
      "  int aa[int];\n"
      "  int r1[$], r2[$], r3[$], r4[$];\n"
      "  initial begin\n"
      "    aa[0] = 5; aa[1] = -3;\n"
      "    r1 = q.max with (item - 1);\n"
      "    r2 = q.min with (unsigned'(item));\n"
      "    r3 = aa.min with (item * 2);\n"
      "    r4 = aa.max with (unsigned'(item));\n"
      "    $display(\"%0d %0d %0d %0d\", r1[0], r2[0], r3[0], r4[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 5 -3 -3\n");
}

TEST(ArrayLocator, TheIteratorReadsWithTheElementTypesSignedness) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int d[] = '{5, -3};\n"
      "  int f[2] = '{5, -3};\n"
      "  int q[$] = '{5, -3};\n"
      "  bit [31:0] u[$] = '{5, -3};\n"
      "  int aa[int], as[string];\n"
      "  int r1[$], r2[$], r3[$], r4[$], r5[$], r6[$];\n"
      "  initial begin\n"
      "    aa[0] = 5; aa[1] = -3; as[\"a\"] = 5; as[\"b\"] = -3;\n"
      "    r1 = d.find with (item < 0);\n"
      "    r2 = f.find_index with (item < 0);\n"
      "    r3 = q.map() with (int'(item < 0));\n"
      "    r4 = u.find with (item < 0);\n"
      "    r5 = aa.find with (item < 0);\n"
      "    r6 = as.find_first with (item < 0);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", r1[0], r2[0], r3[1],\n"
      "             r4.size(), r5[0], r6[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 1 1 0 -3 -3\n");
}

TEST(ArrayLocator, TheIteratorOfAnAssociativeMapReadsSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int aa[int], ma[int];\n"
      "  int as[string], ms[string];\n"
      "  initial begin\n"
      "    aa[0] = -3; as[\"a\"] = -3;\n"
      "    ma = aa.map() with (int'(item < 0));\n"
      "    ms = as.map() with (int'(item < 0));\n"
      "    $display(\"%0d %0d\", ma[0], ms[\"a\"]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(ArrayLocator, AnOptionalWithClauseReadsTheIteratorsMembers) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int x; int y;} s_t;\n"
      "  s_t q[$] = '{'{1, 10}, '{-2, 20}, '{3, 30}, '{1, 40}};\n"
      "  s_t f[3] = '{'{1, 10}, '{-2, 20}, '{3, 30}};\n"
      "  s_t r1[$], r2[$], r3[$];\n"
      "  int r4[$];\n"
      "  initial begin\n"
      "    r1 = q.max with (item.x);\n"
      "    r2 = f.min with (item.x);\n"
      "    r3 = q.unique with (item.x);\n"
      "    r4 = q.unique_index with (item.x);\n"
      "    $display(\"%0d %0d %0d %0d\", r1[0].y, r2[0].y, r3.size(), r4[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "30 20 3 2\n");
}

TEST(ArrayLocator, AnAssociativeLocatorReadsTheIteratorsMembers) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int x; int y;} s_t;\n"
      "  s_t aa[int], as[string];\n"
      "  s_t r1[$], r2[$], r3[$], r4[$];\n"
      "  initial begin\n"
      "    aa[0] = '{1, 10}; aa[1] = '{-2, 20}; aa[2] = '{3, 30};\n"
      "    aa[3] = '{1, 40}; as[\"a\"] = '{1, 10}; as[\"b\"] = '{-2, 20};\n"
      "    r1 = aa.max with (item.x);\n"
      "    r2 = aa.find with (item.x == 3);\n"
      "    r3 = as.min with (item.x);\n"
      "    r4 = aa.unique with (item.x);\n"
      "    $display(\"%0d %0d %0d %0d\", r1[0].y, r2.size(), r3[0].y, "
      "r4.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "30 1 20 3\n");
}

}  // namespace
