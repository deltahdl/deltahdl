

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimulationAlgorithmSim,
     ExecuteSimulationAdvancesThroughNonemptyTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t : {0, 5, 10}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 5u);
  EXPECT_EQ(times[2], 10u);
}

TEST(SimulationAlgorithmSim, ExecuteSimulationStopsWhenAllTimeSlotsEmpty) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { count++; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(count, 1);

  EXPECT_FALSE(sched.HasEvents());
}

TEST(SimulationAlgorithmSim, ExecuteTimeSlotFullRegionOrdering) {
  VerifyAllRegionOrder();
}

TEST(SimulationAlgorithmSim, ReactiveRestartsActiveSetBeforePrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_reactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "active_from_reactive");
  EXPECT_EQ(order[2], "pre_postponed");
}

TEST(SimulationAlgorithmSim, ExecuteRegionDrainsAllEventsInFIFOOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  for (int i = 0; i < 5; ++i) {
    EXPECT_EQ(order[i], i);
  }
}

TEST(SimulationAlgorithmSim,
     PrePostponedWaitsForCascadeThroughAllFiveReactiveRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* re_inactive = sched.GetEventPool().Acquire();
    re_inactive->callback = [&]() {
      order.push_back("re_inactive");
      auto* pre_re_nba = sched.GetEventPool().Acquire();
      pre_re_nba->callback = [&]() {
        order.push_back("pre_re_nba");
        auto* re_nba = sched.GetEventPool().Acquire();
        re_nba->callback = [&]() {
          order.push_back("re_nba");
          auto* post_re_nba = sched.GetEventPool().Acquire();
          post_re_nba->callback = [&]() { order.push_back("post_re_nba"); };
          sched.ScheduleEvent(sched.CurrentTime(), Region::kPostReNBA,
                              post_re_nba);
        };
        sched.ScheduleEvent(sched.CurrentTime(), Region::kReNBA, re_nba);
      };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kPreReNBA, pre_re_nba);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReInactive, re_inactive);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* pp = sched.GetEventPool().Acquire();
  pp->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pp);

  sched.Run();
  ASSERT_EQ(order.size(), 6u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "re_inactive");
  EXPECT_EQ(order[2], "pre_re_nba");
  EXPECT_EQ(order[3], "re_nba");
  EXPECT_EQ(order[4], "post_re_nba");
  EXPECT_EQ(order[5], "pre_postponed");
}

TEST(SimulationAlgorithmSim, OuterLoopRestartsWhenPrePostponedSchedulesActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pp = sched.GetEventPool().Acquire();
  pp->callback = [&]() {
    order.push_back("pre_postponed");
    auto* restart = sched.GetEventPool().Acquire();
    restart->callback = [&]() { order.push_back("active_after_pp"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, restart);
  };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pp);

  auto* post = sched.GetEventPool().Acquire();
  post->callback = [&]() { order.push_back("postponed"); };
  sched.ScheduleEvent({0}, Region::kPostponed, post);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "pre_postponed");
  EXPECT_EQ(order[1], "active_after_pp");
  EXPECT_EQ(order[2], "postponed");
}

TEST(SimulationAlgorithmSim, UpdateEventSchedulesEvaluationOfSensitiveProcess) {
  Arena arena;
  Scheduler sched(arena);
  int sampled_value = -1;
  int target = 0;
  std::vector<std::string> order;

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() {
    target = 42;
    order.push_back("update");
    auto* eval = sched.GetEventPool().Acquire();
    eval->kind = EventKind::kEvaluation;
    eval->callback = [&]() {
      sampled_value = target;
      order.push_back("evaluation");
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, eval);
  };
  sched.ScheduleEvent({0}, Region::kActive, update);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "update");
  EXPECT_EQ(order[1], "evaluation");
  EXPECT_EQ(sampled_value, 42);
}

TEST(SimulationAlgorithmSim, IterativeRegionsMatchLrmEnumeration) {
  constexpr Region kExpectedIterative[] = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed};
  for (Region r : kExpectedIterative) {
    EXPECT_TRUE(IsIterativeRegion(r))
        << "Expected iterative region: " << static_cast<int>(r);
  }
  EXPECT_FALSE(IsIterativeRegion(Region::kPreponed));
  EXPECT_FALSE(IsIterativeRegion(Region::kPreActive));
  EXPECT_FALSE(IsIterativeRegion(Region::kPostponed));
}

TEST(SimulationAlgorithmSim, RegionDrainsEventsScheduledDuringExecution) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* first = sched.GetEventPool().Acquire();
  first->callback = [&]() {
    order.push_back(1);
    auto* second = sched.GetEventPool().Acquire();
    second->callback = [&]() {
      order.push_back(2);
      auto* third = sched.GetEventPool().Acquire();
      third->callback = [&]() { order.push_back(3); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, third);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, second);
  };
  sched.ScheduleEvent({0}, Region::kActive, first);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
}

TEST(SimulationAlgorithmSim, ActiveInnerLoopReentersWhenNbaSchedulesActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active_first = sched.GetEventPool().Acquire();
  active_first->callback = [&]() {
    order.push_back("active_first");
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&]() {
      order.push_back("nba");
      auto* active_second = sched.GetEventPool().Acquire();
      active_second->callback = [&]() { order.push_back("active_second"); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active_second);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active_first);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { order.push_back("postponed"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active_first");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "active_second");
  EXPECT_EQ(order[3], "postponed");
}

TEST(SimulationAlgorithmSim,
     ReactiveInnerLoopReentersWhenReNbaSchedulesReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive_first = sched.GetEventPool().Acquire();
  reactive_first->callback = [&]() {
    order.push_back("reactive_first");
    auto* re_nba = sched.GetEventPool().Acquire();
    re_nba->callback = [&]() {
      order.push_back("re_nba");
      auto* reactive_second = sched.GetEventPool().Acquire();
      reactive_second->callback = [&]() { order.push_back("reactive_second"); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kReactive,
                          reactive_second);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReNBA, re_nba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive_first);

  auto* pp = sched.GetEventPool().Acquire();
  pp->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pp);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "reactive_first");
  EXPECT_EQ(order[1], "re_nba");
  EXPECT_EQ(order[2], "reactive_second");
  EXPECT_EQ(order[3], "pre_postponed");
}

TEST(SimulationAlgorithmSim, FutureTimeSlotCreatedDuringExecutionIsAdvancedTo) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  auto* now = sched.GetEventPool().Acquire();
  now->callback = [&]() {
    times.push_back(sched.CurrentTime().ticks);
    auto* later = sched.GetEventPool().Acquire();
    later->callback = [&]() { times.push_back(sched.CurrentTime().ticks); };
    sched.ScheduleEvent({5}, Region::kActive, later);
  };
  sched.ScheduleEvent({0}, Region::kActive, now);

  sched.Run();
  ASSERT_EQ(times.size(), 2u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 5u);
}

}  // namespace
