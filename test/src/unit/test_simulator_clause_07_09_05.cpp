#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_assoc_first_last.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocArrayLast, LastReturnsLargestKey) {
  SimFixture f;
  auto [aa, ref] = MakeAssocWith3Entries(f);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

TEST(AssocArrayLast, LastReturnsZeroOnEmpty) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocArrayLast, ByteIndexLastReturnsOneForByteRef) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 8;
  aa->int_data[50] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[200] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("ix", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "ix");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 200u);
}

TEST(AssocArrayLast, LastStringKeyReturnsLast) {
  SimFixture f;
  MakeAssocWith3StringEntries(f);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

// §7.9.5 — for a string-keyed array, last() must select the lexicographically
// greatest key, not merely some key. Observed by checking that the assigned
// index changes once a new greatest key is added: a bug that returned the
// smallest key would leave the assigned index unchanged.
TEST(AssocArrayLast, LastStringKeyTracksGreatestKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["banana"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("s", 48);
  ref->value = MakeLogic4VecVal(f.arena, 48, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "s");
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  ASSERT_EQ(out.ToUint64(), 1u);
  uint64_t greatest_before = ref->value.ToUint64();
  // Add a key that is now the greatest; last() must follow it.
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 3);
  ASSERT_TRUE(TryEvalAssocMethodCall(call, f.ctx, f.arena, out));
  ASSERT_EQ(out.ToUint64(), 1u);
  EXPECT_NE(ref->value.ToUint64(), greatest_before);
}

TEST(AssocArrayLast, LastStringKeyEmptyReturnsZero) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, true);
  auto* ref = f.ctx.CreateVariable("s", 48);
  ref->value = MakeLogic4VecVal(f.arena, 48, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocArrayLast, LastNoRefArgReturnsZero) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "last");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

}  // namespace
