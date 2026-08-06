#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

using namespace delta;

TEST(PliPostponedSim, PostponedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPostponedSim, ReadOnlySynchCallbackMapsToPostponedRegion) {
  EXPECT_EQ(RegionForPliCallback(kCbReadOnlySynch), Region::kPostponed);
}

TEST(PliPostponedSim, PliWriteFromPostponedRecordsWriteViolation) {
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

  auto* pli_cb = sched.GetEventPool().Acquire();
  pli_cb->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 7;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_cb);

  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 1u);
}

TEST(PliPostponedSim, PliScheduleIntoEarlierRegionIsFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* pli_cb = sched.GetEventPool().Acquire();
  pli_cb->callback = [&]() {
    auto* offender = sched.GetEventPool().Acquire();
    offender->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPrePostponed, offender);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_cb);

  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 1u);
}

TEST(PliPostponedSim, PliScheduleIntoFutureTimeSlotIsNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* pli_cb = sched.GetEventPool().Acquire();
  pli_cb->callback = [&]() {
    auto* future = sched.GetEventPool().Acquire();
    future->callback = []() {};
    sched.ScheduleEvent({1}, Region::kActive, future);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_cb);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
}

TEST(PliPostponedSim, PliScheduleIntoSameRegionAtCurrentTimeIsNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* pli_cb = sched.GetEventPool().Acquire();
  pli_cb->callback = [&]() {
    auto* same_region = sched.GetEventPool().Acquire();
    same_region->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPostponed, same_region);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_cb);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
}

TEST(PliPostponedSim, PostponedInfrastructureWithFullRegionChain) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kPrePostponed, "pre_postponed", order);
  ScheduleLabeled(sched, Region::kPostReNBA, "post_re_nba", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kPreponed, "preponed", order);

  sched.Run();
  std::vector<std::string> expected = {
      "preponed", "active",      "post_nba",      "observed", "post_observed",
      "reactive", "post_re_nba", "pre_postponed", "postponed"};
  EXPECT_EQ(order, expected);
}
