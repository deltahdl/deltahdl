#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"

using namespace delta;

TEST(DeterminismSim, SequentialStatementsExecuteInSourceOrder) {
  VerifyActiveRegionFIFO();
}

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

TEST(DeterminismSim, LargeSequentialBlockPreservesOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 20; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 20u);
  for (int i = 0; i < 20; ++i) {
    EXPECT_EQ(order[i], i);
  }
}

TEST(DeterminismSim, NBAExecutionOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> nba_order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&nba_order, i]() { nba_order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(nba_order.size(), 3u);
  EXPECT_EQ(nba_order[0], 0);
  EXPECT_EQ(nba_order[1], 1);
  EXPECT_EQ(nba_order[2], 2);
}

TEST(DeterminismSim, NBALastAssignmentWins) {
  Arena arena;
  Scheduler sched(arena);
  int a = -1;

  auto* nba0 = sched.GetEventPool().Acquire();
  nba0->callback = [&]() { a = 0; };
  sched.ScheduleEvent({0}, Region::kNBA, nba0);

  auto* nba1 = sched.GetEventPool().Acquire();
  nba1->callback = [&]() { a = 1; };
  sched.ScheduleEvent({0}, Region::kNBA, nba1);

  sched.Run();
  EXPECT_EQ(a, 1);
}

TEST(DeterminismSim, ActiveGeneratedNBAsExecuteInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> nba_order;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    for (int i = 0; i < 3; ++i) {
      auto* nba = sched.GetEventPool().Acquire();
      nba->callback = [&nba_order, i]() { nba_order.push_back(i); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(nba_order.size(), 3u);
  EXPECT_EQ(nba_order[0], 0);
  EXPECT_EQ(nba_order[1], 1);
  EXPECT_EQ(nba_order[2], 2);
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

TEST(DeterminismSim, SourceOrderPreservedAcrossTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 2; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("t0_" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  for (int i = 0; i < 2; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("t5_" + std::to_string(i));
    };
    sched.ScheduleEvent({5}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "t0_0");
  EXPECT_EQ(order[1], "t0_1");
  EXPECT_EQ(order[2], "t5_0");
  EXPECT_EQ(order[3], "t5_1");
}

TEST(DeterminismSim, NBAOrderingAcrossTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> values;
  int a = -1;

  auto* nba0a = sched.GetEventPool().Acquire();
  nba0a->callback = [&]() { a = 10; };
  sched.ScheduleEvent({0}, Region::kNBA, nba0a);

  auto* nba0b = sched.GetEventPool().Acquire();
  nba0b->callback = [&]() { a = 20; };
  sched.ScheduleEvent({0}, Region::kNBA, nba0b);

  auto* sample0 = sched.GetEventPool().Acquire();
  sample0->callback = [&]() { values.push_back(a); };
  sched.ScheduleEvent({0}, Region::kPostponed, sample0);

  auto* nba5a = sched.GetEventPool().Acquire();
  nba5a->callback = [&]() { a = 30; };
  sched.ScheduleEvent({5}, Region::kNBA, nba5a);

  auto* nba5b = sched.GetEventPool().Acquire();
  nba5b->callback = [&]() { a = 40; };
  sched.ScheduleEvent({5}, Region::kNBA, nba5b);

  auto* sample5 = sched.GetEventPool().Acquire();
  sample5->callback = [&]() { values.push_back(a); };
  sched.ScheduleEvent({5}, Region::kPostponed, sample5);

  sched.Run();
  ASSERT_EQ(values.size(), 2u);
  EXPECT_EQ(values[0], 20);
  EXPECT_EQ(values[1], 40);
}

TEST(DeterminismSim, ReactiveNBAExecutionOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kReNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], 0);
  EXPECT_EQ(order[1], 1);
  EXPECT_EQ(order[2], 2);
}

TEST(SchedulingSemanticsSim, ComputationChainInProcess) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = 16'd1;\n"
      "    x = x + 16'd1;\n"
      "    x = x * 16'd3;\n"
      "    x = x - 16'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");

  EXPECT_EQ(result, 5u);
}
