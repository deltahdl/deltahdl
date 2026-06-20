#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocTraversal, FirstReturnsZeroOnEmpty) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocTraversal, FirstReturnsOneWhenWidthSufficient) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[42] = MakeLogic4VecVal(f.arena, 32, 99);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 42u);
}

TEST(AssocTraversal, FirstReturnsSmallestKey) {
  SimFixture f;
  auto [aa, ref] = MakeAssocWith3Entries(f);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 10u);
}

TEST(AssocTraversal, ByteIndexFirstReturnsOneForByteRef) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 8;
  aa->int_data[200] = MakeLogic4VecVal(f.arena, 32, 99);
  auto* ref = f.ctx.CreateVariable("ix", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "ix");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 200u);
}

TEST(AssocTraversal, FirstStringKeyReturnsFirst) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 3);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["banana"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("s", 48);
  ref->value = MakeLogic4VecVal(f.arena, 48, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(AssocTraversal, FirstStringKeyEmptyReturnsZero) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, true);
  auto* ref = f.ctx.CreateVariable("s", 48);
  ref->value = MakeLogic4VecVal(f.arena, 48, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocTraversal, FirstNoRefArgReturnsZero) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "first");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

}  // namespace
