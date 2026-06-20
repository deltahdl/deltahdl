#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_assoc_traversal.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocTraversal, PrevReturnsZeroAtBegin) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {20, 2}}, 10);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
  // §7.9.7 — with no predecessor the index variable must be left untouched.
  EXPECT_EQ(ref->value.ToUint64(), 10u);
}

TEST(AssocTraversal, PrevReturnsZeroOnEmptyArray) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {}, 5);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
  EXPECT_EQ(ref->value.ToUint64(), 5u);
}

TEST(AssocTraversal, PrevFindsLargestSmallerIndex) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {30, 2}, {50, 3}}, 50);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

TEST(AssocTraversal, PrevStringKey) {
  SimFixture f;
  auto r = RunAssocStringTraversal(f, {"apple", "banana", "cherry"}, "cherry",
                                   "prev");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 1u);
}

TEST(AssocTraversal, PrevStringKeyUnchangedAtBegin) {
  SimFixture f;
  auto saved = MakeAssocStringKeyVec(f.arena, "apple").ToUint64();
  auto r = RunAssocStringTraversal(f, {"apple"}, "apple", "prev");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 0u);
  EXPECT_EQ(r.ref_after, saved);
}

TEST(AssocTraversal, PrevNoRefArgReturnsZero) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "prev");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

// §7.9.7 — prev() compares by value ("largest index whose value is smaller
// than the given index argument"), so the argument itself need not be a stored
// index. Here 40 lies between the stored keys 30 and 50.
TEST(AssocTraversal, PrevArgumentNeedNotBeStoredIndex) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {30, 2}, {50, 3}}, 40);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

// §7.9.7 — when the argument value exceeds every stored index, the largest
// stored index is still strictly smaller than it, so prev() returns that last
// index and the function returns 1.
TEST(AssocTraversal, PrevArgumentAboveAllKeysReturnsLast) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {20, 2}, {30, 3}}, 100);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

// §7.9.7 — the same value-based rule for string keys. "banana" is not stored
// but sorts between the stored keys "apple" and "cherry"; the predecessor is
// "apple".
TEST(AssocTraversal, PrevStringArgumentNeedNotBeStoredIndex) {
  SimFixture f;
  auto r = RunAssocStringTraversal(f, {"apple", "cherry"}, "banana", "prev");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 1u);
  // Predecessor of "banana" is "apple".
  uint64_t expected = MakeAssocStringKeyVec(f.arena, "apple").ToUint64();
  EXPECT_EQ(r.ref_after, expected);
}

}  // namespace
