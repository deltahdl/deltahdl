#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

// §7.9.5: last() assigns largest index and returns 1.
TEST(AssocTraversal, LastReturnsLargestKey) {
  SimFixture f;
  auto [aa, ref] = MakeAssocWith3Entries(f);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "last", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 30u);
}

// §7.9.5: last() returns 0 on empty array.
TEST(AssocTraversal, LastReturnsZeroOnEmpty) {
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

}  // namespace
