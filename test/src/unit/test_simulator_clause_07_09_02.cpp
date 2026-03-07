#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

// §7.9.2: delete(key) removes one entry.
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

// §7.9.2: delete() with no args clears all entries.
TEST(AssocMethods, DeleteNoArgClearsAll) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["world"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* call = MkAssocCallNoArg(f.arena, "aa", "delete");
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->str_data.size(), 0u);
}

// §7.9.2: delete(key) on nonexistent key is a no-op.
TEST(AssocMethods, DeleteNonexistentKeyIsNoop) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 100);
  auto* call = MkAssocCallInt(f.arena, "aa", "delete", 999);
  TryExecAssocMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data.count(10), 1u);
}

}  // namespace
