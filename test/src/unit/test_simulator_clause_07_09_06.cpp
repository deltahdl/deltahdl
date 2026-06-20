#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_assoc_traversal.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocTraversal, NextReturnsZeroAtEnd) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {20, 2}}, 20);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
  EXPECT_EQ(ref->value.ToUint64(), 20u);
}

TEST(AssocTraversal, NextReturnsZeroOnEmptyArray) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {}, 5);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
  EXPECT_EQ(ref->value.ToUint64(), 5u);
}

TEST(AssocTraversal, NextFindsSmallestGreaterIndex) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {30, 2}, {50, 3}}, 10);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

TEST(AssocTraversal, NextStringKeyUnchangedAtEnd) {
  SimFixture f;
  auto saved = MakeAssocStringKeyVec(f.arena, "apple").ToUint64();
  auto r = RunAssocStringTraversal(f, {"apple"}, "apple", "next");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 0u);
  EXPECT_EQ(r.ref_after, saved);
}

TEST(AssocTraversal, NextNoRefArgReturnsZero) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "next");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocTraversal, NextArgumentNeedNotBeStoredIndex) {
  SimFixture f;
  auto [aa, ref] = MakeAssocIntEntries(f, {{10, 1}, {30, 2}, {50, 3}}, 20);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

TEST(AssocTraversal, NextStringArgumentNeedNotBeStoredIndex) {
  SimFixture f;
  // "banana" sorts between the two stored keys but is not itself stored.
  auto r = RunAssocStringTraversal(f, {"apple", "cherry"}, "banana", "next");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 1u);
}

TEST(AssocTraversal, NextStringKey) {
  SimFixture f;
  auto r = RunAssocStringTraversal(f, {"apple", "banana", "cherry"}, "apple",
                                   "next");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 1u);
}

// §7.9.6 — on success the ref index variable is updated to the successor key.
// The string-key success tests above only check the return code; this asserts
// the assignment half of the rule by reading back the key written into ref.
TEST(AssocTraversal, NextStringAssignsSuccessorKey) {
  SimFixture f;
  auto r = RunAssocStringTraversal(f, {"apple", "banana", "cherry"}, "apple",
                                   "next");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.out.ToUint64(), 1u);

  // Successor of "apple" is "banana"; ref must now hold that encoding.
  uint64_t expected = MakeAssocStringKeyVec(f.arena, "banana").ToUint64();
  EXPECT_EQ(r.ref_after, expected);
}

}  // namespace
