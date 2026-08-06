#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

// Checks that the queue named "arr" holds exactly the expected element values.
void ExpectQueueValues(SimFixture& f, const std::vector<uint64_t>& expected) {
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), expected.size());
  for (size_t i = 0; i < expected.size(); ++i) {
    EXPECT_EQ(q->elements[i].ToUint64(), expected[i]);
  }
}

// Registers a 3-element fixed array "arr", seeds its elements with `in`, runs
// the ordering property `op`, then checks the elements against `expected`.
void RunFixedArray3(SimFixture& f, const char* op,
                    const std::array<uint64_t, 3>& in,
                    const std::array<uint64_t, 3>& expected) {
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray("arr", info);
  // SimContext::variables_ is keyed by std::string_view, so the name backing
  // each element variable must outlive the context use below. Keep the three
  // element names in a stable container rather than recreating transient
  // std::strings (whose freed buffers would leave the map keys dangling).
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

// ---------------------------------------------------------------------------
// §7.12.2 end-to-end: the ordering methods reorder an array produced by
// ordinary declaration/initializer syntax, driven through the full pipeline
// (parse, elaborate, lower, run). The synthetic cases above hand-register an
// array and invoke the executor directly; these prove the same production
// paths fire when the receiver is a real declared array and the method appears
// as a procedural statement. A dynamically sized array (int a[]) exercises the
// "dynamically sized" input form and a fixed-bound array the "fixed" form;
// §7.12.2 names both. A dynamic array is queue-backed, so its elements are
// read back through the queue after the run.
// ---------------------------------------------------------------------------

// Runs `src` to completion and returns the elements of the queue-backed array
// `name` as unsigned values.
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

// §7.12.2: shuffle() randomizes the order without adding or dropping elements,
// so a full run must leave the same multiset of values behind.
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

// §7.12.2: with an optional with clause, sort() orders by the expression value
// rather than the element value. Ascending on key (10 - item) inverts the
// natural element order, so the result confirms the with expression governs
// the sort when it is written in real source and evaluated at run time.
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

// §7.12.2: rsort() applies the same optional with-clause key but ranks it in
// descending order. On key (10 - item) the descending key order recovers the
// natural ascending element order.
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

// §7.12.2: the "fixed ... sized" input form. A fixed-bound unpacked array is
// sorted in place; reading the elements back after the run observes the
// reorder through the ordinary element-select path.
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

// §7.12.2: a queue ([$]) is a dynamically sized unpacked array, so the ordering
// methods apply to it too. The array cases above route through the fixed/
// dynamic-array executor; a queue is reordered by a separate production path
// (the queue property dispatch), so it is observed independently here. These
// use the no-parenthesis property form the LRM examples themselves show
// (e.g. q.sort), driven from a real queue declaration and initializer.

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

// §7.12.2: the with-clause ordering key must apply to the parenthesis-free
// member form too (the LRM writes `c.sort with (...)`). Ascending on key
// (10 - item) inverts the natural element order, proving the with expression —
// not the raw element value — drives the sort even without parentheses.
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

// §7.12.2: the with-clause key must also apply when the receiver is a queue,
// which reaches evaluation through a distinct path than fixed/dynamic arrays.
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

// §7.12.2: rsort() ranks the same with-clause key in descending order; on a
// queue, key (10 - item) descending recovers ascending element order.
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

}  // namespace
