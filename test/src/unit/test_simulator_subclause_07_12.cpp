#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
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

TEST(ArrayMethodWithClause, DefaultIndexNameIsIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {50, 60, 70, 80});

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

TEST(ArrayMethodWithClause, CustomIteratorNameBindsElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});

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

TEST(ArrayMethodWithClause, CustomIndexNameSelectsByPosition) {
  SimFixture f;
  MakeDynArray(f, "arr", {50, 60, 70, 80});

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

TEST(ArrayMethodWithClause, IteratorArgumentWithoutWithClauseIsError) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3});

  auto* call = MakeMethodCall(f.arena, "arr", "find", {MakeId(f.arena, "x")});
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  EXPECT_FALSE(ok);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "iterator argument without 'with' clause", 0,
                            "7.12"));
}

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

TEST(ArrayMethodWithClause, LocatorIteratorWithoutWithNames7_12) {
  SimFixture f;
  MakeDynArray(f, "arr", {7, 8});
  auto* call = MakeMethodCall(f.arena, "arr", "find", {MakeId(f.arena, "e")});
  std::vector<Logic4Vec> out;
  TryCollectLocatorResult(call, f.ctx, f.arena, out);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "iterator argument without 'with' clause", 0,
                            "7.12"));
}

TEST(ArrayMethodWithClause, OrderingIteratorWithoutWithNames7_12) {
  SimFixture f;
  MakeDynArray(f, "arr", {9, 4});
  auto* call = MakeMethodCall(f.arena, "arr", "sort", {MakeId(f.arena, "e")});
  TryExecArrayMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "iterator argument without 'with' clause", 0,
                            "7.12"));
}

TEST(ArrayMethodsSim, ManipulationMethodsOnAQueueProperty) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int q[$];\n"
      "    function void fill(); q = {7, 2, 9}; endfunction\n"
      "    function int big(); int b[$]; b = q.find with (item > 5);\n"
      "      return b.size() * 100 + q.sum(); endfunction\n"
      "  endclass\n"
      "  C h; int b[$];\n"
      "  initial begin\n"
      "    h = new; h.fill();\n"
      "    b = h.q.find with (item > 5);\n"
      "    $display(\"%0d %0d %0d %0d\", h.big(), h.q.sum(), b.size(), b[1]);\n"
      "    h.q.sort();\n"
      "    $display(\"%0d %0d %0d\", h.q[0], h.q[1], h.q[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "218 18 2 9\n2 7 9\n");
}

TEST(ArrayMethodsSim, ReadingMethodsOnArrayPropertiesThroughAHandle) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int d[];\n"
      "    int f[4];\n"
      "    function void fill(); d = new[3]; d[0] = 7; d[1] = 2; d[2] = 9;\n"
      "      f[0] = 5; f[1] = 1; f[2] = 8; f[3] = 3;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h; int mx[$], ix[$], mn[$];\n"
      "  initial begin\n"
      "    h = new; h.fill();\n"
      "    mx = h.d.max; ix = h.f.find_first_index with (item > 6);\n"
      "    mn = h.f.min;\n"
      "    $display(\"%0d %0d %0d %0d\", mx[0], ix[0], mn[0], h.f.sum());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 2 1 17\n");
}

TEST(ArrayMethodsSim, MethodResultIsAReceiver) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string SA[5] = '{\"a\", \"b\", \"a\", \"c\", \"b\"};\n"
      "  int IA[int], q[$];\n"
      "  initial begin\n"
      "    IA[0] = 9; IA[1] = 2; IA[2] = 9; IA[3] = 5;\n"
      "    q = IA.find(x) with (x > 5).unique;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", SA.unique().size(), q.size(),\n"
      "             q[0], IA.min()[0], IA.find with (item == 9).size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 9 2 2\n");
}

TEST(ArrayMethodsSim, MethodResultElementKeepsItsSign) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int IA[int];\n"
      "  initial begin\n"
      "    IA[0] = -3;\n"
      "    $display(\"%0d %0d\", IA.min()[0], IA.min()[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 1\n");
}

}  // namespace
