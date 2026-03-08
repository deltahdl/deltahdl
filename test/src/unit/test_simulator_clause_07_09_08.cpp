#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

// Create assoc array with 32-bit index and an 8-bit ref variable "k".
std::pair<AssocArrayObject*, Variable*> MakeNarrowRefAssoc(SimFixture& f) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  auto* ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  return {aa, ref};
}

// §7.9.8: first() returns -1 when ref is narrower than index.
TEST(AssocTraversalArgs, FirstReturnsTruncationFlag) {
  SimFixture f;
  auto [aa, ref] = MakeNarrowRefAssoc(f);
  aa->int_data[1000] = MakeLogic4VecVal(f.arena, 32, 42);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  // Ref gets least significant 8 bits of 1000.
  EXPECT_EQ(ref->value.ToUint64(), 1000u & 0xFFu);
}

// §7.9.8: last() returns -1 when ref is narrower than index.
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

// §7.9.8: next() returns -1 when ref is narrower than index.
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

// §7.9.8: prev() returns -1 when ref is narrower than index.
TEST(AssocTraversalArgs, PrevReturnsTruncationFlag) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[400] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[500] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(500 & 0xFF));
  // prev() from 500: finds predecessor 400, which also truncates.
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "prev", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 400u & 0xFFu);
}

// §7.9.8: No truncation when ref width >= index width (returns 1).
TEST(AssocTraversalArgs, FirstReturnsOneWhenWidthSufficient) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 8;
  aa->int_data[200] = MakeLogic4VecVal(f.arena, 32, 99);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 200u);
}

// §7.9.8: No truncation when ref width == index width (returns 1).
TEST(AssocTraversalArgs, LastReturnsOneWhenWidthEqual) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[42] = MakeLogic4VecVal(f.arena, 32, 10);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 42u);
}

// §7.9.8: Truncation with 16-bit ref and 32-bit index.
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

// §7.9.8: No truncation when key fits in narrower ref.
TEST(AssocTraversalArgs, NoTruncationWhenKeyFitsInNarrowRef) {
  SimFixture f;
  auto [aa, ref] = MakeNarrowRefAssoc(f);
  // Key 5 fits in 8 bits, but index_width (32) > ref width (8) → still -1.
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 99);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  // Returns -1 based on type widths, not actual key value.
  EXPECT_EQ(out.ToUint64(), static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_EQ(ref->value.ToUint64(), 5u);
}

// §7.9.8: Truncation preserves LSBs per the LRM example (1000 → 232).
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
  // 1000 & 0xFF = 232 (least significant 8 bits of 1000).
  EXPECT_EQ(ref->value.ToUint64(), 232u);
}

}  // namespace
