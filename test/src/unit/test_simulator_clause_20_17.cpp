// §20.17: Miscellaneous tasks and functions

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, SystemReturnsExitCode) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$system", {MkStr(f.arena, "true")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, SystemFailureExitCode) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$system", {MkStr(f.arena, "false")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.ToUint64(), 0u);
}

TEST(SysTask, StacktraceDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stacktrace", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

}  // namespace
