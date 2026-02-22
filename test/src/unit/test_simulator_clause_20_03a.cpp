// §20.3: Simulation time system functions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

struct SysTaskFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MkSysCall(Arena &arena, std::string_view name,
                       std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

namespace {

TEST(SysTask, TimeReturnsCurrentTicks) {
  SysTaskFixture f;
  auto *event = f.scheduler.GetEventPool().Acquire();
  event->callback = []() {};
  f.scheduler.ScheduleEvent(SimTime{100}, Region::kActive, event);
  auto *expr = MkSysCall(f.arena, "$time", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.width, 64u);
}

TEST(SysTask, StimeReturns32Bit) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$stime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, RealtimeReturns64Bit) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$realtime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
}

}  // namespace
