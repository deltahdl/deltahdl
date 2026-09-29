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

// ---------------------------------------------------------------------------
// §7.12 Syntax 7-5 writes the argument list of an array method call as
// optional, so `q.sort` and `q.sort()` are one call, and §7.12.2 gives that one
// call the same effect on a queue whichever way it is spelled. The two
// spellings reach evaluation through different productions -- a call
// expression and a member reference -- so each is stated on its own, and the
// pair is what says they are one call rather than two methods.
// ---------------------------------------------------------------------------

// §7.12 Syntax 7-5 with §7.12.2: sort() written with its (empty) argument list
// orders the queue in ascending order.
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

// §7.12 Syntax 7-5 with §7.12.2: the same sort() call written without the
// argument list orders the same queue the same way. Paired with the
// parenthesized case above, this is the claim that Syntax 7-5's optional
// argument list leaves one call with one effect.
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

// §7.12 Syntax 7-5 with §7.12.2: reverse() written with its (empty) argument
// list reverses the order of the queue's elements.
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

// §7.12 Syntax 7-5 with §7.12.2: shuffle() written with its (empty) argument
// list randomizes the order of the queue's elements and neither adds nor drops
// one, so the multiset of values is what holds for every permutation the draw
// could produce.
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

// §7.12.2: specifying a with clause on reverse() is an error, and the report
// it raises names §7.12.2 -- the subclause that says so of both reverse() and
// shuffle().
TEST(ArrayOrdering, ReverseWithClauseErrorNames7_12_2) {
  SimFixture f;
  MakeDynArray(f, "arr", {3, 1, 2});
  auto* call = MakeMethodCall(f.arena, "arr", "reverse", {});
  call->with_expr = MakeId(f.arena, "item");
  TryExecArrayMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "does not accept a 'with' clause", 0, "7.12.2"));
}

// ---------------------------------------------------------------------------
// §7.10.3 over the §7.12.2 ordering methods, on a dynamic array. §7.12.2 gives
// sort(), rsort(), reverse() and shuffle() to any unpacked array, and none of
// them removes an element. §7.10.3 therefore keeps every outstanding element
// reference valid across one, and a valid reference stays attached to the
// element it was taken on rather than to the index that element sat at. A
// dynamic array is backed by the same QueueObject a queue is, and a `ref`
// argument is recorded against the identity of the element it was taken on, so
// an ordering method that moves the values without moving those identities
// makes a later write through the reference land on whichever element moved
// into the old index -- a different element from the one the reference names.
// ---------------------------------------------------------------------------

// §7.10.3 with §7.12.2: sort() removes nothing, so the reference taken on the
// element holding 30 stays valid and follows that element to the back, where
// sorting {30, 10, 20} puts it. The write of 99 has to land there rather than
// at index 0, the index the reference was taken at.
TEST(ArrayOrdering, SortLeavesDynArrayRefFollowingItsElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 20});

  RunQueueRefMethodThenAssign(f, "arr", "sort", {}, 0);

  ExpectQueueValues(f, {10u, 20u, 99u});
}

// §7.10.3 with §7.12.2: reverse() removes nothing either, and it moves the
// element holding 30 from the front of {30, 10, 20} to the back. The reference
// taken on that element follows it, so the write of 99 lands at the back.
TEST(ArrayOrdering, ReverseLeavesDynArrayRefFollowingItsElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 20});

  RunQueueRefMethodThenAssign(f, "arr", "reverse", {}, 0);

  ExpectQueueValues(f, {20u, 10u, 99u});
}

// §7.10.3 with §7.12.2: shuffle() removes nothing, so the reference taken on
// the element holding 30 stays valid and the write of 99 replaces that element
// wherever the permutation put it. The permutation is not predictable, so the
// claim is stated as what holds for every one of them: 99 is in the array once
// and 30, the value the reference was taken on, is gone. A write that landed on
// whichever element moved into index 0 would leave 30 behind.
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

// §7.12 with §7.2: the iterator of a with clause over an array of structures
// holds a structure, so `item.red` is its member -- sort orders a fixed array
// and a queue by it, find keeps the elements whose member matches, and sum
// adds the members.
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

// §7.12.2 with §6.16: sort and rsort order a queue of strings
// lexicographically -- apple, fig, pear -- and not by the packed value that
// puts a shorter string first.
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

// §7.12.2 with §6.16: sort and rsort reorder a fixed-size or dynamic array
// of strings, each element keeping its text.
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

// §7.12.2 with §6.11: sort() and rsort() order the elements of a signed type
// as signed numbers, -3 below 5, in a queue, a dynamic array and a fixed-size
// array alike, and the elements of an unsigned type as unsigned ones, -3
// written into a `bit [31:0]` element then being 4294967293, above 5.
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

// §7.12.2: with a with clause, sort() and rsort() order by the clause's value,
// as signed where the expression is signed -- the iterator reading as the
// element type -- and as unsigned where it is not.
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

}  // namespace
