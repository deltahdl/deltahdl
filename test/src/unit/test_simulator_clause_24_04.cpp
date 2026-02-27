// §24.4: Eliminating testbench races

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// §24.11 Reactive region context flag
// =============================================================================
TEST(ProgramSim, ReactiveContextFlag) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  // No current process => not reactive.
  EXPECT_FALSE(ctx.IsReactiveContext());

  // Process with is_reactive = true => reactive context.
  Process proc;
  proc.is_reactive = true;
  ctx.SetCurrentProcess(&proc);
  EXPECT_TRUE(ctx.IsReactiveContext());

  // Process with is_reactive = false => not reactive.
  Process non_reactive;
  non_reactive.is_reactive = false;
  ctx.SetCurrentProcess(&non_reactive);
  EXPECT_FALSE(ctx.IsReactiveContext());

  ctx.SetCurrentProcess(nullptr);
}

}  // namespace
