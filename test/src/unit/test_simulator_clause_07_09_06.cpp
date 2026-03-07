#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

// §7.9.6: next() finds smallest index greater than given.
TEST(AssocTraversal, NextFindsSuccessor) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 3);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 10);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 20u);
}

// §7.9.6: next() returns 0 when at last element.
TEST(AssocTraversal, NextReturnsZeroAtEnd) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 20);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

// §7.9.6: next() on string-keyed array.
TEST(AssocTraversal, NextStringKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["banana"] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 3);
  // Set ref to "apple" (string key in Logic4Vec form).
  auto* ref = f.ctx.CreateVariable("s", 48);
  // Encode "apple" as a 5-byte Logic4Vec.
  auto v = MakeLogic4Vec(f.arena, 40);
  v.words[0].aval = (uint64_t('a') << 32) | (uint64_t('p') << 24) |
                     (uint64_t('p') << 16) | (uint64_t('l') << 8) |
                     uint64_t('e');
  ref->value = v;
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

}  // namespace
