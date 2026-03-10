
#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

std::pair<AssocArrayObject*, Variable*> MakeNarrowRefAssoc(SimFixture& f) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  auto* ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  return {aa, ref};
}

namespace {

TEST(AssocTraversalArgs, FirstReturnsTruncationFlag) {
  SimFixture f;
  auto [aa, ref] = MakeNarrowRefAssoc(f);
  aa->int_data[1000] = MakeLogic4VecVal(f.arena, 32, 42);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));

  EXPECT_EQ(ref->value.ToUint64(), 1000u & 0xFFu);
}

TEST(AssocTraversalArgs, LastReturnsTruncationFlag) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[500] = MakeLogic4VecVal(f.arena, 32, 10);
  auto* ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 500u & 0xFFu);
}

TEST(AssocTraversalArgs, NextReturnsTruncationFlag) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[300] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 10);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "next", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 300u & 0xFFu);
}

TEST(AssocTraversalArgs, PrevReturnsTruncationFlag) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[400] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[500] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("k", 16);
  ref->value = MakeLogic4VecVal(f.arena, 16, 500);

  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 400u);
}

TEST(AssocTraversalArgs, FirstTruncatesTo16Bit) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[70000] = MakeLogic4VecVal(f.arena, 32, 7);
  auto* ref = f.ctx.CreateVariable("ix", 16);
  ref->value = MakeLogic4VecVal(f.arena, 16, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "ix");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 70000u & 0xFFFFu);
}

TEST(AssocTraversalArgs, NoTruncationWhenKeyFitsInNarrowRef) {
  SimFixture f;
  auto [aa, ref] = MakeNarrowRefAssoc(f);

  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 99);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);

  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 5u);
}

TEST(AssocTraversalArgs, TruncationPreservesLSBsLRMExample) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[1000] = MakeLogic4VecVal(f.arena, 32, 0);
  auto* ref = f.ctx.CreateVariable("ix", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "ix");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));

  EXPECT_EQ(ref->value.ToUint64(), 232u);
}

}  // namespace
