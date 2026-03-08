#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocMethods, NumReturnsCount) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 3);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "num");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(AssocMethods, SizeReturnsCount) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["world"] = MakeLogic4VecVal(f.arena, 32, 2);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "size");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 2u);
}

TEST(AssocMethods, NumReturnsZeroForEmpty) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  Logic4Vec out{};
  auto* call = MkAssocCallNoArg(f.arena, "aa", "num");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

}
