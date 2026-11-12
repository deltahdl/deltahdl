#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingScopeSim, BlockPersistsAcrossClockEdges) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x10);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x10u);

  data->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

TEST(ClockingScopeSim, ABlockOfAnAutomaticModuleKeepsItsSamplesStatically) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module automatic sub(input logic clk);\n"
                       "  int d = 5;\n"
                       "  clocking cb @(posedge clk); input d; endclocking\n"
                       "  initial begin\n"
                       "    @(cb); d = 6;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  sub u(clk);\n"
                       "  initial #11 $display(\"%0d\", u.cb.d);\n"
                       "  initial #21 begin $display(\"%0d\", u.cb.d); "
                       "$finish; end\n"
                       "endmodule\n",
                       f),
            "5\n6\n$finish at time 21\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
