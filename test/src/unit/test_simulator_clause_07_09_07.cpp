#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocTraversal, PrevFindsPredecessor) {
  SimFixture f;
  auto [aa, ref] = MakeAssocWith3Entries(f);
  ref->value = MakeLogic4VecVal(f.arena, 32, 30);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 20u);
}

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

}  // namespace
