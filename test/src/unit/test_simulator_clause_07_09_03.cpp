#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/adv_sim.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AdvSim, AssocArrayExistsAndErase) {
  AssocArray arr;
  arr.Insert("k", 1);
  EXPECT_TRUE(arr.Exists("k"));
  EXPECT_FALSE(arr.Exists("other"));
  arr.Erase("k");
  EXPECT_FALSE(arr.Exists("k"));
  EXPECT_EQ(arr.Size(), 0u);
}

TEST(AssocMethods, ExistsReturnsTrueForPresentIntKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 100);
  Logic4Vec out{};
  auto* call = MkAssocCallInt(f.arena, "aa", "exists", 10);
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(AssocMethods, ExistsReturnsFalseForMissingIntKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 100);
  Logic4Vec out{};
  auto* call = MkAssocCallInt(f.arena, "aa", "exists", 999);
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocMethods, ExistsReturnsTrueForPresentStringKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call = MkAssocCallNoArg(f.arena, "aa", "exists");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kStringLiteral;
  arg->text = "hello";
  call->args.push_back(arg);
  Logic4Vec out{};
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(AssocMethods, ExistsReturnsFalseForMissingStringKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  auto* call = MkAssocCallNoArg(f.arena, "aa", "exists");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kStringLiteral;
  arg->text = "missing";
  call->args.push_back(arg);
  Logic4Vec out{};
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocMethods, ExistsOnEmptyArrayReturnsFalse) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  Logic4Vec out{};
  auto* call = MkAssocCallInt(f.arena, "aa", "exists", 0);
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(AssocMethods, ExistsAfterDeleteReturnsFalse) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[42] = MakeLogic4VecVal(f.arena, 32, 99);

  Logic4Vec out{};
  auto* call_exists = MkAssocCallInt(f.arena, "aa", "exists", 42);
  TryEvalAssocMethodCall(call_exists, f.ctx, f.arena, out);
  EXPECT_EQ(out.ToUint64(), 1u);

  auto* call_del = MkAssocCallInt(f.arena, "aa", "delete", 42);
  TryExecAssocMethodStmt(call_del, f.ctx, f.arena);

  Logic4Vec out2{};
  auto* call_exists2 = MkAssocCallInt(f.arena, "aa", "exists", 42);
  TryEvalAssocMethodCall(call_exists2, f.ctx, f.arena, out2);
  EXPECT_EQ(out2.ToUint64(), 0u);
}

}  // namespace
