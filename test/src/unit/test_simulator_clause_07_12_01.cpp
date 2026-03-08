#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

// Build arr.method with (predicate) expression.
static Expr* MakeLocatorExpr(Arena& arena, std::string_view var,
                             std::string_view method, Expr* with_expr) {
  auto* call = MakeMethodCall(arena, var, method, {});
  call->with_expr = with_expr;
  return call;
}

namespace {

// §7.12.1: unique returns distinct elements.
TEST(ArrayLocator, UniqueReturnsDistinct) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 10, 30, 20});
  auto* expr = MakeMethodCall(f.arena, "arr", "unique", {});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(expr, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 3u);
}

// §7.12.1: unique_index returns indices of first occurrences.
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

// §7.12.1: find with predicate returns matching elements.
TEST(ArrayLocator, FindWithPredicate) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 15, 25, 35});
  // with (item > 10)
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

// §7.12.1: find_first returns only first match.
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

// §7.12.1: find_last returns last match.
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

// §7.12.1: find_index returns indices of all matches.
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

// §7.12.1: find_last_index returns index of last match.
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

// §7.12.1: find with no matches returns empty.
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

}  // namespace
