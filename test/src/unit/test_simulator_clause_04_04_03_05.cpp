#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

using namespace delta;

TEST(PliPreObservedSim, PreObservedCanReadValues) {
  VerifyRegionCanReadActiveValue(Region::kPreObserved);
}

TEST(PliPreObservedSim, PreObservedReadsAfterActiveRegionSetStabilized) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { value = 77; };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, ev);

  sched.Run();
  EXPECT_EQ(sampled, 77);
}

TEST(PliPreObservedSim, PreObservedExecutesAfterPostNBABeforeObserved) {
  VerifyThreeRegionOrder({Region::kPostNBA, "post_nba"},
                         {Region::kPreObserved, "pre_observed"},
                         {Region::kObserved, "observed"});
}

TEST(PliPreObservedSim, PreObservedExecutesAfterEntireActiveRegionSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "post_nba");
  EXPECT_EQ(order[3], "pre_observed");
}

TEST(PliPreObservedSim, PreObservedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreObservedSim, PreObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreObservedSim, PreObservedReadsFullyStabilizedActiveSetState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto set_final = [&]() { value = 99; };
  auto schedule_reentry = [&]() {
    auto* active2 = sched.GetEventPool().Acquire();
    active2->callback = set_final;
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    if (value == 0) {
      value = 1;
      auto* inactive = sched.GetEventPool().Acquire();
      inactive->callback = schedule_reentry;
      sched.ScheduleEvent({0}, Region::kInactive, inactive);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sampled, 99);
}

// §4.4.3.5: within the Pre-Observed region it is illegal to schedule an event
// within the current time slot. Scheduling into the current time slot from a
// Pre-Observed callback is recorded as a violation.
TEST(PliPreObservedSim, ScheduleIntoCurrentTimeSlotFromPreObservedIsFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kObserved, ev);
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  EXPECT_EQ(sched.IllegalPreObservedScheduleCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedScheduleCount(), 1u);
}

TEST(PliPreObservedSim, MultipleIllegalSchedulesFromPreObservedAreEachCounted) {
  Arena arena;
  Scheduler sched(arena);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    for (int i = 0; i < 3; ++i) {
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = []() {};
      sched.ScheduleEvent(sched.CurrentTime(), Region::kObserved, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedScheduleCount(), 3u);
}

// Scheduling an event at a future time slot from a Pre-Observed callback is
// legal - the restriction only bars events in the current time slot.
TEST(PliPreObservedSim, FutureScheduleFromPreObservedIsNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    auto* future = sched.GetEventPool().Acquire();
    future->callback = []() {};
    sched.ScheduleEvent({1}, Region::kActive, future);
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedScheduleCount(), 0u);
}

// A schedule into the current time slot from a non-Pre-Observed region carries
// no Pre-Observed violation.
TEST(PliPreObservedSim, ScheduleFromActiveIsNotFlaggedAgainstPreObserved) {
  Arena arena;
  Scheduler sched(arena);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedScheduleCount(), 0u);
}

// §4.4.3.5: within the Pre-Observed region it is illegal to write values to any
// net or variable. A VPI write performed from a Pre-Observed callback is
// recorded as a violation.
TEST(PliPreObservedSim, VpiPutValueFromPreObservedRecordsWriteViolation) {
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

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 42;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 1u);
}

TEST(PliPreObservedSim, MultipleIllegalWritesFromPreObservedAreEachCounted) {
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

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    for (int i = 0; i < 4; ++i) {
      VpiValue value{};
      value.format = kVpiIntVal;
      value.value.integer = i;
      vpi.PutValue(&obj, &value, nullptr, 0);
    }
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 4u);
}

// A VPI write from a writable region (e.g. Post-NBA, see §4.4.3.4) carries no
// Pre-Observed violation.
TEST(PliPreObservedSim, VpiPutValueFromPostNbaIsNotFlaggedAgainstPreObserved) {
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

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 7;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 0u);
}

// §4.4.3.5 bars scheduling into the current time slot outright - unlike the
// Preponed region, there is no exemption for scheduling back into the same
// region. An event scheduled into Pre-Observed itself at the current time is
// still a violation (the re-entrant event itself is harmless and runs).
TEST(PliPreObservedSim,
     ScheduleIntoSamePreObservedRegionAtCurrentTimeIsFlagged) {
  Arena arena;
  Scheduler sched(arena);
  bool inner_ran = false;

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    auto* inner = sched.GetEventPool().Acquire();
    inner->callback = [&]() { inner_ran = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPreObserved, inner);
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  EXPECT_TRUE(inner_ran);
  EXPECT_EQ(sched.IllegalPreObservedScheduleCount(), 1u);
}

// §4.4.3.5 forbids writing "any net or variable" from the region. A VPI write
// to a net (rather than a variable) from a Pre-Observed callback is likewise
// recorded as a write violation.
TEST(PliPreObservedSim, VpiPutValueOnNetFromPreObservedRecordsWriteViolation) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Net net{};
  VpiObject obj{};
  obj.net = &net;

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 1;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 1u);
}
