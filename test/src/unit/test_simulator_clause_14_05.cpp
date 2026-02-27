// §14.5: Hierarchical expressions

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/clocking.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"
#include "helpers_clocking.h"

using namespace delta;

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.

// Schedule negedge at a given time through the scheduler.

namespace {

// =============================================================================
// 12. Hierarchical access to clocking signals (S14.10)
// =============================================================================
TEST(ClockingSim, HierarchicalAccess) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xCC);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr, "cb", Edge::kPosedge, {0}, {0}, "data_in", ClockingDir::kInput);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  auto sampled = cmgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xCCu);
}

}  // namespace
