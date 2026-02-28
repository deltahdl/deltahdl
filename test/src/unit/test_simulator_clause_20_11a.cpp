// §20.11: Assertion control system tasks

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, AssertOnDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$asserton", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertOffDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertoff", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertKillDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertkill", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertControlDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertcontrol", {MkInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

}  // namespace
