#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(AssocMethods, DeleteByKeyRemovesEntry) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 200);
  auto* call = MkAssocCallInt(f.arena, "aa", "delete", 10);
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->int_data.count(10), 0u);
  EXPECT_EQ(aa->int_data.count(20), 1u);
}

TEST(AssocMethods, DeleteNoArgClearsAll) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["world"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call = MkAssocCallNoArg(f.arena, "aa", "delete");
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->str_data.size(), 0u);
}

TEST(AssocMethods, DeleteNonexistentKeyIsNoop) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 100);
  auto* call = MkAssocCallInt(f.arena, "aa", "delete", 999);
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data.count(10), 1u);
}

TEST(AssocMethods, DeleteByKeyStringKeyed) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["world"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* expr = MkAssocCallNoArg(f.arena, "aa", "delete");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kStringLiteral;
  arg->text = "hello";
  expr->args.push_back(arg);
  TryExecAssocMethodStmt(expr, f.ctx, f.arena);
  EXPECT_EQ(aa->str_data.count("hello"), 0u);
  EXPECT_EQ(aa->str_data.count("world"), 1u);
}

TEST(AssocMethods, DeleteNoArgClearsAllIntKeyed) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call = MkAssocCallNoArg(f.arena, "aa", "delete");
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->int_data.size(), 0u);
}

TEST(AssocMethods, DeleteNonexistentKeyStringKeyed) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  auto* expr = MkAssocCallNoArg(f.arena, "aa", "delete");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kStringLiteral;
  arg->text = "missing";
  expr->args.push_back(arg);
  TryExecAssocMethodStmt(expr, f.ctx, f.arena);
  EXPECT_EQ(aa->str_data.size(), 1u);
  EXPECT_EQ(aa->str_data.count("hello"), 1u);
}

TEST(AssocMethods, DeletePropertySyntaxClearsAll) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 2);
  bool ok = TryExecAssocPropertyStmt("aa", "delete", f.ctx, f.arena);
  ASSERT_TRUE(ok);
  EXPECT_EQ(aa->int_data.size(), 0u);
}

TEST(AssocMethods, DeleteOnlyEntryLeavesEmptyArray) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[42] = MakeLogic4VecVal(f.arena, 32, 99);
  auto* call = MkAssocCallInt(f.arena, "aa", "delete", 42);
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->int_data.size(), 0u);
}

TEST(AssocMethods, DeleteNoArgOnEmptyArrayIsNoop) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);
  auto* call = MkAssocCallNoArg(f.arena, "aa", "delete");
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  // No crash, no error — just a no-op.
}

}  // namespace
