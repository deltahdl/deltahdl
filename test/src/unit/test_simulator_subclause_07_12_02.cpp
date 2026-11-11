#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_queue_ref_method.h"
#include "helpers_reported_error.h"
#include "simulator/eval_array.h"
#include "simulator/sim_context_types.h"

using namespace delta;

namespace {

void ExpectQueueValues(SimFixture& f, const std::vector<uint64_t>& expected) {
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), expected.size());
  for (size_t i = 0; i < expected.size(); ++i) {
    EXPECT_EQ(q->elements[i].ToUint64(), expected[i]);
  }
}

void RunFixedArray3(SimFixture& f, const char* op,
                    const std::array<uint64_t, 3>& in,
                    const std::array<uint64_t, 3>& expected) {
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray("arr", info);
  std::array<std::string, 3> names{"arr[0]", "arr[1]", "arr[2]"};
  for (uint32_t i = 0; i < 3; ++i) {
    MakeVar(f, names[i], 32, 0);
  }
  for (uint32_t i = 0; i < 3; ++i) {
    f.ctx.FindVariable(names[i])->value = MakeLogic4VecVal(f.arena, 32, in[i]);
  }
  TryExecArrayPropertyStmt("arr", op, f.ctx, f.arena);
  for (uint32_t i = 0; i < 3; ++i) {
    EXPECT_EQ(f.ctx.FindVariable(names[i])->value.ToUint64(), expected[i]);
  }
}

TEST(ArrayOrdering, SortAscending) {
  SimFixture f;
  MakeDynArray(f, "arr", {40, 10, 30, 20});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  ExpectQueueValues(f, {10u, 20u, 30u, 40u});
}

TEST(ArrayOrdering, SortAlreadySorted) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3, 4});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  ExpectQueueValues(f, {1u, 2u, 3u, 4u});
}

TEST(ArrayOrdering, SortSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  ExpectQueueValues(f, {42u});
}

TEST(ArrayOrdering, SortEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  ExpectQueueValues(f, {});
}

TEST(ArrayOrdering, SortDuplicateValues) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 30, 10});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  ExpectQueueValues(f, {10u, 10u, 30u, 30u});
}

TEST(ArrayOrdering, SortFixedArray) {
  SimFixture f;
  RunFixedArray3(f, "sort", {30, 10, 20}, {10u, 20u, 30u});
}

TEST(ArrayOrdering, RsortDescending) {
  SimFixture f;
  MakeDynArray(f, "arr", {40, 10, 30, 20});
  TryExecArrayPropertyStmt("arr", "rsort", f.ctx, f.arena);
  ExpectQueueValues(f, {40u, 30u, 20u, 10u});
}

TEST(ArrayOrdering, RsortFixedArray) {
  SimFixture f;
  RunFixedArray3(f, "rsort", {10, 30, 20}, {30u, 20u, 10u});
}

TEST(ArrayOrdering, ReverseOrder) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  ExpectQueueValues(f, {30u, 20u, 10u});
}

TEST(ArrayOrdering, ReverseSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  ExpectQueueValues(f, {42u});
}

TEST(ArrayOrdering, ReverseEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  ExpectQueueValues(f, {});
}

TEST(ArrayOrdering, ReverseTwiceRestoresOriginal) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  ExpectQueueValues(f, {10u, 20u, 30u, 40u});
}

TEST(ArrayOrdering, ReverseFixedArray) {
  SimFixture f;
  RunFixedArray3(f, "reverse", {0xAA, 0xBB, 0xCC}, {0xCC, 0xBB, 0xAA});
}

TEST(ArrayOrdering, ShufflePreservesElements) {
  SimFixtureSeeded f;
  auto* q = f.ctx.CreateQueue("arr", 32);
  for (uint64_t v : {10u, 20u, 30u, 40u, 50u}) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = 5;
  f.ctx.RegisterArray("arr", info);
  TryExecArrayPropertyStmt("arr", "shuffle", f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 5u);

  uint64_t sum = 0;
  for (auto& e : q->elements) sum += e.ToUint64();
  EXPECT_EQ(sum, 150u);
}

TEST(ArrayOrdering, ShuffleEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  TryExecArrayPropertyStmt("arr", "shuffle", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(ArrayOrdering, ShuffleSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  TryExecArrayPropertyStmt("arr", "shuffle", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

std::vector<uint64_t> RunAndReadElems(SimFixture& f, const char* src,
                                      const char* name) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return {};
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue(name);
  EXPECT_NE(q, nullptr);
  std::vector<uint64_t> out;
  if (q != nullptr)
    for (auto& e : q->elements) out.push_back(e.ToUint64());
  return out;
}

TEST(ArrayOrderingE2E, SortAscendingReordersDeclaredArray) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{40, 10, 30, 20};\n"
                             "  initial a.sort();\n"
                             "endmodule\n",
                             "a");
  EXPECT_EQ(got, (std::vector<uint64_t>{10u, 20u, 30u, 40u}));
}

TEST(ArrayOrderingE2E, RsortDescendingReordersDeclaredArray) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{40, 10, 30, 20};\n"
                             "  initial a.rsort();\n"
                             "endmodule\n",
                             "a");
  EXPECT_EQ(got, (std::vector<uint64_t>{40u, 30u, 20u, 10u}));
}

TEST(ArrayOrderingE2E, ReverseReordersDeclaredArray) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{10, 20, 30};\n"
                             "  initial a.reverse();\n"
                             "endmodule\n",
                             "a");
  EXPECT_EQ(got, (std::vector<uint64_t>{30u, 20u, 10u}));
}

TEST(ArrayOrderingE2E, ShufflePreservesMultisetOfDeclaredArray) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{10, 20, 30, 40, 50};\n"
                             "  initial a.shuffle();\n"
                             "endmodule\n",
                             "a");
  std::sort(got.begin(), got.end());
  EXPECT_EQ(got, (std::vector<uint64_t>{10u, 20u, 30u, 40u, 50u}));
}

TEST(ArrayOrderingE2E, SortWithExpressionOrdersByKeyNotElement) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{3, 1, 2};\n"
                             "  initial a.sort(item) with (10 - item);\n"
                             "endmodule\n",
                             "a");
  EXPECT_EQ(got, (std::vector<uint64_t>{3u, 2u, 1u}));
}

TEST(ArrayOrderingE2E, RsortWithExpressionOrdersByKeyNotElement) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{3, 1, 2};\n"
                             "  initial a.rsort(item) with (10 - item);\n"
                             "endmodule\n",
                             "a");
  EXPECT_EQ(got, (std::vector<uint64_t>{1u, 2u, 3u}));
}

TEST(ArrayOrderingE2E, SortReordersDeclaredFixedArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr[0:2] = '{30, 10, 20};\n"
      "  int a0, a1, a2;\n"
      "  initial begin\n"
      "    arr.sort();\n"
      "    a0 = arr[0];\n"
      "    a1 = arr[1];\n"
      "    a2 = arr[2];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a0")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("a1")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("a2")->value.ToUint64(), 30u);
}

TEST(ArrayOrderingE2E, SortAscendingReordersDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{4, 5, 3, 1};\n"
                             "  initial q.sort;\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{1u, 3u, 4u, 5u}));
}

TEST(ArrayOrderingE2E, RsortDescendingReordersDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{4, 5, 3, 1};\n"
                             "  initial q.rsort;\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{5u, 4u, 3u, 1u}));
}

TEST(ArrayOrderingE2E, ReverseReordersDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{10, 20, 30};\n"
                             "  initial q.reverse;\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{30u, 20u, 10u}));
}

TEST(ArrayOrderingE2E, ShufflePreservesMultisetOfDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{10, 20, 30, 40, 50};\n"
                             "  initial q.shuffle;\n"
                             "endmodule\n",
                             "q");
  std::sort(got.begin(), got.end());
  EXPECT_EQ(got, (std::vector<uint64_t>{10u, 20u, 30u, 40u, 50u}));
}

TEST(ArrayOrderingE2E, SortWithExpressionNoParenMemberFormOnArray) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int a[] = '{3, 1, 2};\n"
                             "  initial a.sort with (10 - item);\n"
                             "endmodule\n",
                             "a");
  EXPECT_EQ(got, (std::vector<uint64_t>{3u, 2u, 1u}));
}

TEST(ArrayOrderingE2E, SortWithExpressionOnDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{3, 1, 2};\n"
                             "  initial q.sort with (10 - item);\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{3u, 2u, 1u}));
}

TEST(ArrayOrderingE2E, RsortWithExpressionOnDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{3, 1, 2};\n"
                             "  initial q.rsort with (10 - item);\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{1u, 2u, 3u}));
}

TEST(ArrayOrderingE2E, SortCallWithParensReordersDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{30, 10, 20};\n"
                             "  initial q.sort();\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{10u, 20u, 30u}));
}

TEST(ArrayOrderingE2E, SortCallWithoutParensReordersDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{30, 10, 20};\n"
                             "  initial q.sort;\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{10u, 20u, 30u}));
}

TEST(ArrayOrderingE2E, ReverseCallWithParensReordersDeclaredQueue) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{10, 20, 30};\n"
                             "  initial q.reverse();\n"
                             "endmodule\n",
                             "q");
  EXPECT_EQ(got, (std::vector<uint64_t>{30u, 20u, 10u}));
}

TEST(ArrayOrderingE2E, ShuffleCallWithParensPreservesQueueMultiset) {
  SimFixture f;
  auto got = RunAndReadElems(f,
                             "module m;\n"
                             "  int q[$] = '{10, 20, 30, 40, 50};\n"
                             "  initial q.shuffle();\n"
                             "endmodule\n",
                             "q");
  std::sort(got.begin(), got.end());
  EXPECT_EQ(got, (std::vector<uint64_t>{10u, 20u, 30u, 40u, 50u}));
}

TEST(ArrayOrdering, ReverseWithClauseErrorNames7_12_2) {
  SimFixture f;
  MakeDynArray(f, "arr", {3, 1, 2});
  auto* call = MakeMethodCall(f.arena, "arr", "reverse", {});
  call->with_expr = MakeId(f.arena, "item");
  TryExecArrayMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not accept a 'with' clause", 0, "7.12.2"));
}

TEST(ArrayOrdering, SortLeavesDynArrayRefFollowingItsElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 20});

  RunQueueRefMethodThenAssign(f, "arr", "sort", {}, 0);

  ExpectQueueValues(f, {10u, 20u, 99u});
}

TEST(ArrayOrdering, ReverseLeavesDynArrayRefFollowingItsElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 20});

  RunQueueRefMethodThenAssign(f, "arr", "reverse", {}, 0);

  ExpectQueueValues(f, {20u, 10u, 99u});
}

TEST(ArrayOrdering, ShuffleLeavesDynArrayRefValid) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 20});

  RunQueueRefMethodThenAssign(f, "arr", "shuffle", {}, 0);

  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  size_t wrote = 0, kept = 0;
  for (const auto& e : q->elements) {
    if (e.ToUint64() == 99u) ++wrote;
    if (e.ToUint64() == 30u) ++kept;
  }
  EXPECT_EQ(wrote, 1u);
  EXPECT_EQ(kept, 0u);
}

TEST(ArrayOrderingSim, WithClauseReadsAMemberOfAStructElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { byte red, green, blue; } c_t;\n"
      "  c_t c[3] = '{'{3, 0, 0}, '{1, 0, 0}, '{2, 0, 0}};\n"
      "  c_t q[$], r[$];\n"
      "  int s;\n"
      "  initial begin\n"
      "    q.push_back('{7, 1, 1}); q.push_back('{5, 2, 2});\n"
      "    r = c.find with (item.red > 1);\n"
      "    s = c.sum with (int'(item.red));\n"
      "    c.sort with (item.red);\n"
      "    q.sort with (item.red);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", c[0].red, c[1].red,\n"
      "             c[2].red, q[0].red, q[1].green, r.size(), s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 5 1 2 6\n");
}

TEST(ArrayOrderingSim, SortOrdersAStringQueueLexicographically) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string q[$] = {\"pear\", \"apple\", \"fig\"};\n"
      "  string r[$] = {\"pear\", \"apple\", \"fig\"};\n"
      "  initial begin\n"
      "    q.sort(); r.rsort();\n"
      "    $display(\"%s %s %s %s %s %s\", q[0], q[1], q[2], r[0], r[1],\n"
      "             r[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "apple fig pear pear fig apple\n");
}

TEST(ArrayOrderingSim, SortKeepsTheStringsOfAnArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string fa[3] = '{\"pear\", \"apple\", \"fig\"};\n"
      "  string d[] = '{\"pear\", \"apple\", \"fig\"};\n"
      "  initial begin\n"
      "    fa.sort(); d.rsort();\n"
      "    $display(\"%s %s %s %s %s %s\", fa[0], fa[1], fa[2], d[0], d[1],\n"
      "             d[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "apple fig pear pear fig apple\n");
}

TEST(ArrayOrderingSim, SortAndRsortOrderByTheElementTypesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$] = '{5, -3};\n"
      "  int d[] = '{5, -3};\n"
      "  int f[2] = '{5, -3};\n"
      "  bit [31:0] u[$] = '{-3, 5};\n"
      "  initial begin\n"
      "    q.sort(); d.sort(); f.sort(); u.sort();\n"
      "    $display(\"%0d %0d %0d %0d\", q[0], d[0], f[0], u[0]);\n"
      "    q.rsort(); d.rsort(); f.rsort(); u.rsort();\n"
      "    $display(\"%0d %0d %0d %0d\", q[0], d[0], f[0], u[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 -3 -3 5\n5 5 5 4294967293\n");
}

TEST(ArrayOrderingSim, SortWithAClauseOrdersByTheClausesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$] = '{5, -3};\n"
      "  int d[] = '{5, -3};\n"
      "  int p[$] = '{-3, 5};\n"
      "  int e[] = '{-3, 5};\n"
      "  initial begin\n"
      "    q.sort with (item);\n"
      "    d.sort(x) with (x);\n"
      "    p.rsort with (item);\n"
      "    e.sort(x) with (unsigned'(x));\n"
      "    $display(\"%0d %0d %0d %0d\", q[0], d[0], p[0], e[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 -3 5 5\n");
}

TEST(ArrayOrderingSim, TheCallSpellingOrdersAQueueByItsWithClause) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int dq[$] = '{5, 2, 9, 4};\n"
      "  int dr[$] = '{5, 2, 9, 4};\n"
      "  int dm[$] = '{5, 2, 9, 4};\n"
      "  initial begin\n"
      "    dq.sort(x) with (x % 3);\n"
      "    dr.rsort(x) with (x % 3);\n"
      "    dm.sort with (item % 3);\n"
      "    $display(\"%p %p %p\", dq, dr, dm);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{9, 4, 5, 2} '{5, 2, 4, 9} '{9, 4, 5, 2}\n");
}

TEST(ArrayOrderingSim, OrderingMethodsReorderAClassArrayProperty) {
  SimFixture f;
  auto out = RunCapture(
      "class H;\n"
      "  int arr[4];\n"
      "  byte d[];\n"
      "  string s[3];\n"
      "  function void down(); arr.rsort(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    h.arr = '{5, -2, 9, 4};\n"
      "    h.arr.sort();\n"
      "    $display(\"%0d %0d %0d %0d\", h.arr[0], h.arr[1], h.arr[2], "
      "h.arr[3]);\n"
      "    h.down();\n"
      "    $display(\"%0d %0d %0d %0d\", h.arr[0], h.arr[1], h.arr[2], "
      "h.arr[3]);\n"
      "    h.arr.reverse();\n"
      "    $display(\"%0d %0d %0d %0d\", h.arr[0], h.arr[1], h.arr[2], "
      "h.arr[3]);\n"
      "    h.arr.sort(x) with (x % 3);\n"
      "    $display(\"%0d %0d %0d %0d\", h.arr[0], h.arr[1], h.arr[2], "
      "h.arr[3]);\n"
      "    h.d = '{3, -1, 2};\n"
      "    h.d.sort();\n"
      "    h.s[0] = \"pear\"; h.s[1] = \"apple\"; h.s[2] = \"fig\";\n"
      "    h.s.sort();\n"
      "    $display(\"%0d %0d %0d %s %s %s\", h.d[0], h.d[1], h.d[2], h.s[0], "
      "h.s[1], h.s[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "-2 4 5 9\n9 5 4 -2\n-2 4 5 9\n-2 9 4 5\n-1 2 3 apple fig pear\n");
}

TEST(ArrayOrderingSim, ShuffleReordersAClassArrayPropertysOwnElements) {
  SimFixture f;
  auto out = RunCapture(
      "class H;\n"
      "  int arr[8];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    automatic int moved = 0, kept = 0;\n"
      "    repeat (16) begin\n"
      "      h.arr = '{0, 1, 2, 3, 4, 5, 6, 7};\n"
      "      h.arr.shuffle();\n"
      "      if (h.arr[0] != 0 || h.arr[7] != 7) moved++;\n"
      "      h.arr.sort();\n"
      "      if (h.arr[0] == 0 && h.arr[3] == 3 && h.arr[7] == 7 && "
      "h.arr.sum() == 28) kept++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", moved > 0, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 16\n");
}

TEST(ArrayOrderingSim, SortByAConcatenatedKeyAndAnEnumByItsValue) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  typedef struct { byte red, green, blue; } c_t;\n"
      "  c_t c[4];\n"
      "  typedef enum {A = 3, B = 1, C = 2} e_t;\n"
      "  e_t e[3] = '{A, B, C};\n"
      "  initial begin\n"
      "    c[0] = '{1, 9, 2}; c[1] = '{2, 1, 2};\n"
      "    c[2] = '{3, 5, 1}; c[3] = '{4, 0, 2};\n"
      "    c.sort(x) with ({x.blue, x.green});\n"
      "    foreach (c[i]) $write(\"%0d \", c[i].red);\n"
      "    c.rsort with (item.red);\n"
      "    foreach (c[i]) $write(\"%0d \", c[i].red);\n"
      "    e.sort;\n"
      "    $display(\"%p\", e);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 4 2 1 4 3 2 1 '{B, C, A}\n");
}

TEST(ArrayOrderingSim, DISABLED_SortAndRsortOrderRealValuesNumerically) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  real r[$] = {2.5, -1.0, 7.25, 0.5};\n"
      "  shortreal s[3] = '{1.5, -2.0, 0.25};\n"
      "  real d[] = {3.0, -0.5};\n"
      "  int q[$] = {3, -4, 5, 1};\n"
      "  initial begin\n"
      "    r.sort; $display(\"%p\", r);\n"
      "    r.rsort; $display(\"%p\", r);\n"
      "    s.sort; $display(\"%p\", s);\n"
      "    d.rsort; $display(\"%p\", d);\n"
      "    q.sort with (item * -0.5); $display(\"%p\", q);\n"
      "    q.rsort with (real'(item) - 0.5); $display(\"%p\", q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{-1, 0.5, 2.5, 7.25}\n'{7.25, 2.5, 0.5, -1}\n'{-2, 0.25, 1.5}\n"
            "'{3, -0.5}\n'{5, 3, 1, -4}\n'{5, 3, 1, -4}\n");
}

}  // namespace
