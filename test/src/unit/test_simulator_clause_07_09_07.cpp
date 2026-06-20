#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocTraversal, PrevReturnsZeroAtBegin) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 10);
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
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 5);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
  EXPECT_EQ(ref->value.ToUint64(), 5u);
}

TEST(AssocTraversal, PrevFindsLargestSmallerIndex) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[50] = MakeLogic4VecVal(f.arena, 32, 3);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 50);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

TEST(AssocTraversal, PrevStringKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["banana"] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 3);

  auto* ref = f.ctx.CreateVariable("s", 48);

  auto v = MakeLogic4Vec(f.arena, 48);
  v.words[0].aval = (uint64_t('c') << 40) | (uint64_t('h') << 32) |
                    (uint64_t('e') << 24) | (uint64_t('r') << 16) |
                    (uint64_t('r') << 8) | uint64_t('y');
  ref->value = v;
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(AssocTraversal, PrevStringKeyUnchangedAtBegin) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  auto* ref = f.ctx.CreateVariable("s", 48);
  auto v = MakeLogic4Vec(f.arena, 40);
  v.words[0].aval = (uint64_t('a') << 32) | (uint64_t('p') << 24) |
                    (uint64_t('p') << 16) | (uint64_t('l') << 8) |
                    uint64_t('e');
  ref->value = v;
  auto saved = ref->value.ToUint64();
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
  EXPECT_EQ(ref->value.ToUint64(), saved);
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
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[50] = MakeLogic4VecVal(f.arena, 32, 3);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 40);
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
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 3);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 100);
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
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("s", 48);
  auto v = MakeLogic4Vec(f.arena, 48);
  v.words[0].aval = (uint64_t('b') << 40) | (uint64_t('a') << 32) |
                    (uint64_t('n') << 24) | (uint64_t('a') << 16) |
                    (uint64_t('n') << 8) | uint64_t('a');
  ref->value = v;
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  // Predecessor of "banana" is "apple".
  uint64_t expected = (uint64_t('a') << 32) | (uint64_t('p') << 24) |
                      (uint64_t('p') << 16) | (uint64_t('l') << 8) |
                      uint64_t('e');
  EXPECT_EQ(ref->value.ToUint64(), expected);
}

}  // namespace
