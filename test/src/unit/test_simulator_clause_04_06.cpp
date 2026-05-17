#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(DeterminismSim, SuspendedProcessResumesInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* a0 = sched.GetEventPool().Acquire();
  a0->callback = [&]() {
    order.push_back("A0");

    auto* a1 = sched.GetEventPool().Acquire();
    a1->callback = [&]() { order.push_back("A1"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, a1);
  };
  sched.ScheduleEvent({0}, Region::kActive, a0);

  auto* b0 = sched.GetEventPool().Acquire();
  b0->callback = [&]() { order.push_back("B0"); };
  sched.ScheduleEvent({0}, Region::kActive, b0);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "A0");
  EXPECT_EQ(order[1], "B0");

  EXPECT_EQ(order[2], "A1");
}

TEST(DeterminismSim, SequentialStatementsProduceOrderedNBAs) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> log;

  for (int i = 0; i < 3; ++i) {
    auto* stmt = sched.GetEventPool().Acquire();
    stmt->callback = [&, i]() {
      log.push_back("stmt" + std::to_string(i));
      auto* nba = sched.GetEventPool().Acquire();
      nba->callback = [&, i]() { log.push_back("nba" + std::to_string(i)); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
    };
    sched.ScheduleEvent({0}, Region::kActive, stmt);
  }

  sched.Run();

  std::vector<std::string> expected = {"stmt0", "stmt1", "stmt2",
                                       "nba0",  "nba1",  "nba2"};
  EXPECT_EQ(log, expected);
}

TEST(DeterminismSim, BlockingAssignmentsExecuteInSourceOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = a * 8'd2;\n"
      "    c = b + a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 30u);
}

TEST(DeterminismSim, NBAExecutionOrderMatchesSourceOrder) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a <= 8'd0;\n"
      "    a <= 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 1u);
}

TEST(DeterminismSim, SourceOrderPreservedAcrossSuspension) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 32'd0;\n"
      "    #5 x = (x << 4) | 32'd1;\n"
      "    #5 x = (x << 4) | 32'd2;\n"
      "    #5 x = (x << 4) | 32'd3;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x123u);
}

