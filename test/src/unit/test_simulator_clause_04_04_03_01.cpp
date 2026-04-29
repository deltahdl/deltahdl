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

TEST(PliPreponedSim, PreponedAccessesDataBeforeAnyStateChange) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled_in_preponed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_in_preponed = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled_in_preponed, 42);
}

TEST(PliPreponedSim, PreponedSeesStateBeforeAllSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto schedule_mod = [&](Region r, int new_val) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&value, new_val]() { value = new_val; };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule_mod(Region::kActive, 10);
  schedule_mod(Region::kInactive, 20);
  schedule_mod(Region::kNBA, 30);
  schedule_mod(Region::kReactive, 40);
  schedule_mod(Region::kReNBA, 50);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled, 0);
}

TEST(PliPreponedSim, PreponedExecutesBeforePreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { order.push_back("pre_active"); };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { order.push_back("preponed"); };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "pre_active");
}

TEST(PliPreponedSim, PreponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreponedSim, PreponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreponedSim, PreponedProvidesConsistentReadOnlySnapshot) {
  Arena arena;
  Scheduler sched(arena);
  int a = 1;
  int b = 2;
  int sum_in_preponed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 100;
    b = 200;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sum_in_preponed = a + b; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sum_in_preponed, 3);
}

// §4.4.3.1: scheduling into another region of the current time slot from
// inside Preponed is illegal. The scheduler records the violation.
TEST(PliPreponedSim, IllegalScheduleIntoOtherRegionInCurrentTimeSlot) {
  Arena arena;
  Scheduler sched(arena);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    auto* offender = sched.GetEventPool().Acquire();
    offender->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, offender);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 1u);
}

// §4.4.3.1: scheduling into the same region (Preponed) at the current time
// slot is not the "any other region" case, so it is not flagged. Likewise,
// scheduling into another region at a *future* time slot is allowed because
// the restriction is scoped to the current time slot.
TEST(PliPreponedSim, LegalSchedulesFromPreponedAreNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    auto* future = sched.GetEventPool().Acquire();
    future->callback = []() {};
    sched.ScheduleEvent({1}, Region::kActive, future);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 0u);
}

// §4.4.3.1: scheduling from non-Preponed regions (e.g. Active) into other
// regions of the current time slot is permitted by §4.4.3.1 — the rule is
// specific to the Preponed region.
TEST(PliPreponedSim, ScheduleFromActiveIntoOtherRegionIsNotFlagged) {
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
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 0u);
}

// §4.4.3.1: each illegal schedule from Preponed is counted independently.
TEST(PliPreponedSim, MultipleIllegalSchedulesAreEachCounted) {
  Arena arena;
  Scheduler sched(arena);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    for (int i = 0; i < 3; ++i) {
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = []() {};
      sched.ScheduleEvent(sched.CurrentTime(), Region::kPreActive, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 3u);
}

// §4.4.3.1: while executing Preponed, the scheduler reports the current
// region so the restriction can be inspected by code paths that emit nets
// or variable writes.
TEST(PliPreponedSim, CurrentRegionIsPreponedDuringPreponedCallback) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(observed, Region::kPreponed);
}

// §4.4.3.1: the rule forbids scheduling into "any other region" within the
// current time slot — the Preponed region itself is not "other" and must not
// be flagged.
TEST(PliPreponedSim, ScheduleIntoSamePreponedRegionAtCurrentTimeIsNotFlagged) {
  Arena arena;
  Scheduler sched(arena);
  bool inner_ran = false;

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    auto* inner = sched.GetEventPool().Acquire();
    inner->callback = [&]() { inner_ran = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPreponed, inner);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_TRUE(inner_ran);
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 0u);
}

// §4.4.3.1: "any other region" includes the last region of the time slot —
// the Postponed region. Scheduling into Postponed from inside Preponed at
// the current time slot is a violation.
TEST(PliPreponedSim, ScheduleIntoPostponedAtCurrentTimeIsFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    auto* postponed = sched.GetEventPool().Acquire();
    postponed->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPostponed, postponed);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 1u);
}

// §4.4.3.1: it is illegal to write values to any net or variable from inside
// the Preponed region. The VPI write path (VpiContext::PutValue) is the
// canonical PLI write entry point; when invoked from a Preponed callback,
// the scheduler records the violation.
TEST(PliPreponedSim, VpiPutValueFromPreponedRecordsWriteViolation) {
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

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 42;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 1u);
}

// §4.4.3.1: VPI writes from regions other than Preponed are not flagged —
// the rule is scoped to the Preponed region.
TEST(PliPreponedSim, VpiPutValueOutsidePreponedDoesNotRecordViolation) {
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

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 42;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 0u);
  EXPECT_EQ(var.value.words[0].aval, 42u);
}
