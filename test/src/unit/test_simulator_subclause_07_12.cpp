#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_scheduler.h"
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

// §7.12 head: an iterator_argument optionally renames the per-element variable
// used by the 'with' expression. Naming it "x" instead of the default "item"
// binds the candidate element to "x" for the duration of the with clause.
TEST(ArrayMethodWithClause, CustomIteratorNameBindsElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});

  // arr.find(x) with (x > 25) selects the elements greater than 25.
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "x"),
                          MakeInt(f.arena, 25));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {MakeId(f.arena, "x")});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 30u);
  EXPECT_EQ(out[1].ToUint64(), 40u);
}

// §7.12 head: an index_argument optionally renames the index-query variable.
// Naming the iterator "x" and the index "idx" reaches the position through
// "x.idx" instead of the default "item.index".
TEST(ArrayMethodWithClause, CustomIndexNameSelectsByPosition) {
  SimFixture f;
  MakeDynArray(f, "arr", {50, 60, 70, 80});

  // arr.find(x, idx) with (x.idx > 1) selects positions 2 and 3.
  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "x.idx"),
                          MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "arr", "find",
                              {MakeId(f.arena, "x"), MakeId(f.arena, "idx")});
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

// §7.12 head, end-to-end: the with clause iterates the array elements and
// binds each to the default name `item`. Building the array from a real
// dynamic-array `{...}` initializer (§7.5) and running an array method whose
// with expression scales each element observes the with clause being applied
// by production code through the full pipeline. (2*(1+2+3+4) == 20.)
TEST(ArrayMethodWithClause, WithClauseOverDynamicArrayEndToEnd) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  int q[] = { 1, 2, 3, 4 };\n"
      "  int r;\n"
      "  initial r = q.sum() with (item * 2);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 20u);
}

// §7.12 head, end-to-end with a different input form: a fixed-size unpacked
// array (§7.4) built from an `'{...}` assignment pattern. The default `item`
// name again binds each element for the with expression. ((10+1)+(20+1)+(30+1)
// == 63.)
TEST(ArrayMethodWithClause, WithClauseOverFixedArrayEndToEnd) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  logic [7:0] a [0:2] = '{ 8'd10, 8'd20, 8'd30 };\n"
      "  int r;\n"
      "  initial r = a.sum() with (item + 1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 63u);
}

// §7.12 head, end-to-end: when no index_argument is supplied the iterator index
// is reached through the default name `index`. Summing the positions of a
// real dynamic array observes the default index binding. (0+1+2 == 3.)
TEST(ArrayMethodWithClause, DefaultIndexNameEndToEnd) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  int q[] = { 50, 60, 70 };\n"
      "  int r;\n"
      "  initial r = q.sum() with (item.index);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 3u);
}

// §7.12 head, end-to-end: a named iterator_argument renames the per-element
// variable used by the with expression. Naming it `x` binds each element to
// `x` through the full pipeline. (10+20+30 == 60.)
TEST(ArrayMethodWithClause, CustomIteratorNameEndToEnd) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  int q[] = { 1, 2, 3 };\n"
      "  int r;\n"
      "  initial r = q.sum(x) with (x * 10);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 60u);
}

}  // namespace
