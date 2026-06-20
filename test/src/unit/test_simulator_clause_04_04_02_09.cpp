#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

using namespace delta;

TEST(PostponedRegionSim, PostponedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PostponedRegionSim, PostponedObservesFinalState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 20; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 30; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { value = 40; };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sampled, 40);
}

TEST(PostponedRegionSim, PostponedExecutesAfterAllOtherSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kReNBA, "renba", order);
  ScheduleLabeled(sched, Region::kReInactive, "reinactive", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kInactive, "inactive", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  ASSERT_EQ(order.size(), 8u);
  EXPECT_EQ(order[7], "postponed");
}

TEST(PostponedRegionSim, PostponedIsLastRegionOrdinal) {
  auto postponed_ord = static_cast<int>(Region::kPostponed);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  auto count_ord = static_cast<int>(Region::kCOUNT);
  EXPECT_GT(postponed_ord, pre_postponed_ord);
  EXPECT_EQ(postponed_ord + 1, count_ord);
}

TEST(PostponedRegionSim, PostponedDoesNotReExecuteDuringIteration) {
  Arena arena;
  Scheduler sched(arena);
  int postponed_count = 0;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_count++; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&]() {
      auto* act2 = sched.GetEventPool().Acquire();
      act2->callback = []() {};
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(postponed_count, 1);
}

TEST(PostponedRegionSim, PostponedAdvancesToNextTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* postponed0 = sched.GetEventPool().Acquire();
  postponed0->callback = [&]() { order.push_back("postponed_t0"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed0);

  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { order.push_back("preponed_t1"); };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "postponed_t0");
  EXPECT_EQ(order[1], "preponed_t1");
}

TEST(PostponedRegionSim, PostponedPLIEventsRouteIntoThisRegion) {
  Region pli_target = RegionForPliCallback(kCbReadOnlySynch);
  ASSERT_EQ(pli_target, Region::kPostponed);

  Arena arena;
  Scheduler sched(arena);
  Region pli_observed = Region::kCOUNT;
  Region sim_observed = Region::kCOUNT;

  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&]() { pli_observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, pli_target, pli_ev);

  auto* sim_ev = sched.GetEventPool().Acquire();
  sim_ev->callback = [&]() { sim_observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kPostponed, sim_ev);

  sched.Run();
  EXPECT_EQ(pli_observed, Region::kPostponed);
  EXPECT_EQ(sim_observed, Region::kPostponed);
}

TEST(PostponedRegionSim, PostponedEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kPostponed);
}

TEST(PostponedRegionSim, IllegalScheduleIntoPreviousRegionInCurrentTimeSlot) {
  Arena arena;
  Scheduler sched(arena);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    auto* offender = sched.GetEventPool().Acquire();
    offender->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, offender);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 1u);
}

TEST(PostponedRegionSim, LegalSchedulesFromPostponedAreNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    auto* future = sched.GetEventPool().Acquire();
    future->callback = []() {};
    sched.ScheduleEvent({1}, Region::kActive, future);
    auto* same_region = sched.GetEventPool().Acquire();
    same_region->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPostponed, same_region);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
}

TEST(PostponedRegionSim, MultipleIllegalSchedulesAreEachCounted) {
  Arena arena;
  Scheduler sched(arena);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    for (int i = 0; i < 3; ++i) {
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = []() {};
      sched.ScheduleEvent(sched.CurrentTime(), Region::kPrePostponed, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 3u);
}

TEST(PostponedRegionSim, ScheduleFromActiveIntoEarlierRegionIsNotFlagged) {
  VerifyScheduleFromActiveIsNotFlagged(
      [](Scheduler& s) { return s.IllegalPostponedScheduleCount(); });
}

TEST(PostponedRegionSim, VpiPutValueFromPostponedRecordsWriteViolation) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Logic4Word storage{};
  Variable var{};
  var.value.width = 32;
  var.value.nwords = 1;
  var.value.words = &storage;

  VpiObject obj{};
  obj.var = &var;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 42;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 1u);
}

TEST(PostponedRegionSim, MultipleIllegalWritesAreEachCounted) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Logic4Word storage{};
  Variable var{};
  var.value.width = 32;
  var.value.nwords = 1;
  var.value.words = &storage;

  VpiObject obj{};
  obj.var = &var;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    for (int i = 0; i < 4; ++i) {
      VpiValue value{};
      value.format = kVpiIntVal;
      value.value.integer = i;
      vpi.PutValue(&obj, &value, nullptr, 0);
    }
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 4u);
}

TEST(PostponedRegionSim, VpiPutValueOutsidePostponedDoesNotRecordViolation) {
  VerifyVpiWriteFromActiveIsNotFlagged(
      [](Scheduler& s) { return s.IllegalPostponedWriteCount(); });
}

TEST(PostponedRegionSim, StrobeIsScheduledIntoPostponedRegion) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());

  LowerFixture f;
  std::string snapshot_at_pre_postponed;
  auto* spy = f.scheduler.GetEventPool().Acquire();
  spy->callback = [&]() { snapshot_at_pre_postponed = captured.str(); };
  f.scheduler.ScheduleEvent({0}, Region::kPrePostponed, spy);

  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $strobe(\"DELTA_STROBE_TAG\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  std::cout.rdbuf(old_buf);

  EXPECT_EQ(snapshot_at_pre_postponed.find("DELTA_STROBE_TAG"),
            std::string::npos)
      << "snapshot=" << snapshot_at_pre_postponed;
  EXPECT_NE(captured.str().find("DELTA_STROBE_TAG"), std::string::npos)
      << "captured=" << captured.str();
}

TEST(PostponedRegionSim, MonitorIsScheduledIntoPostponedRegion) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());

  LowerFixture f;
  std::string snapshot_at_pre_postponed;
  auto* spy = f.scheduler.GetEventPool().Acquire();
  spy->callback = [&]() { snapshot_at_pre_postponed = captured.str(); };
  f.scheduler.ScheduleEvent({0}, Region::kPrePostponed, spy);

  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $monitor(\"DELTA_MONITOR_TAG\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  std::cout.rdbuf(old_buf);

  EXPECT_EQ(snapshot_at_pre_postponed.find("DELTA_MONITOR_TAG"),
            std::string::npos)
      << "snapshot=" << snapshot_at_pre_postponed;
  EXPECT_NE(captured.str().find("DELTA_MONITOR_TAG"), std::string::npos)
      << "captured=" << captured.str();
}

TEST(PostponedRegionSim, CurrentRegionIsPostponedDuringPostponedCallback) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(observed, Region::kPostponed);
}
