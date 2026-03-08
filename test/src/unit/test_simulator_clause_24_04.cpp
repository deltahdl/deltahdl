#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(ProgramSim, ReactiveContextFlag) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  EXPECT_FALSE(ctx.IsReactiveContext());

  Process proc;
  proc.is_reactive = true;
  ctx.SetCurrentProcess(&proc);
  EXPECT_TRUE(ctx.IsReactiveContext());

  Process non_reactive;
  non_reactive.is_reactive = false;
  ctx.SetCurrentProcess(&non_reactive);
  EXPECT_FALSE(ctx.IsReactiveContext());

  ctx.SetCurrentProcess(nullptr);
}

}
