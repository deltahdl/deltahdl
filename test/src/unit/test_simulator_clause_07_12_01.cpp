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

TEST(ArrayLocator, FindFirstReturnsLeftmostMatch) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 20});
  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 20));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_first", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 20u);
}

TEST(ArrayLocator, FindLastReturnsRightmostMatch) {
  SimFixture f;
  MakeDynArray(f, "arr", {20, 10, 20, 30});
  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 20));
  auto* expr = MakeLocatorExpr(f.arena, "arr", "find_last", pred);
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 20u);
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

}  // namespace
