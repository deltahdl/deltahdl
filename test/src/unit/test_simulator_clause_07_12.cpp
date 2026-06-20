#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(DynArrayMethod, SizeProperty) {
  SimFixture f;
  MakeDynArray(f, "d", {1, 2, 3});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "size", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(ArrayMethodWithClause, DefaultIteratorNameIsItem) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});

  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 25));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 30u);
  EXPECT_EQ(out[1].ToUint64(), 40u);
}

TEST(ArrayMethodWithClause, IteratorScopeLimitedToWithClause) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  MakeVar(f, "item", 32, 999);

  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "item"),
                          MakeInt(f.arena, 15));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  TryCollectLocatorResult(call, f.ctx, f.arena, out);

  auto* outer_item = f.ctx.FindVariable("item");
  ASSERT_NE(outer_item, nullptr);
  EXPECT_EQ(outer_item->value.ToUint64(), 999u);
}

// §7.12: when no index_argument is supplied, the iterator index is reached
// through the default name 'index' (composed against the iterator as
// item.index). A predicate over that default name selects by position.
TEST(ArrayMethodWithClause, DefaultIndexNameIsIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {50, 60, 70, 80});

  // find with (item.index > 1) selects the elements at positions 2 and 3.
  auto* pred = MakeBinary(f.arena, TokenKind::kGt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 70u);
  EXPECT_EQ(out[1].ToUint64(), 80u);
}

// §7.12: naming an iterator_argument is only meaningful when a 'with' clause
// supplies the expression that consumes it. Supplying the argument without a
// 'with' clause is illegal, so the call is rejected and an error is raised.
TEST(ArrayMethodWithClause, IteratorArgumentWithoutWithClauseIsError) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3});

  // arr.find(x) names an iterator but leaves with_expr null.
  auto* call = MakeMethodCall(f.arena, "arr", "find", {MakeId(f.arena, "x")});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
