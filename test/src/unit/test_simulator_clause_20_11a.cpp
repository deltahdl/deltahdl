// Non-LRM tests

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, AssertControlDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertcontrol", {MkInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

}  // namespace
