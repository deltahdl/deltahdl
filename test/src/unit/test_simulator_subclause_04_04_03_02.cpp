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

TEST(PliPreActiveSim, PreActiveCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 42;
  int sampled = -1;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPreActive, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPreActiveSim, PreActiveCanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() {
    order.push_back("pre_active");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_active"); };
    sched.ScheduleEvent({0}, Region::kActive, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "created_active");
}

TEST(PliPreActiveSim, PreActiveExecutesAfterPreponedBeforeActive) {
  VerifyThreeRegionOrder({Region::kPreponed, "preponed"},
                         {Region::kPreActive, "pre_active"},
                         {Region::kActive, "active"});
}

TEST(PliPreActiveSim, PreActiveRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPreActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPreActiveSim, PreActiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPreActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPreActiveSim, PreActiveReadWriteContrastWithPreponed) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int preponed_sample = -1;
  int active_sample = -1;

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() { value = 55; };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { preponed_sample = value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { active_sample = value; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(preponed_sample, 0);
  EXPECT_EQ(active_sample, 55);
}

// Edge case for "create events before the Active region is evaluated": an event
// created while inside Pre-Active that is itself scheduled into Pre-Active for
// the current time slot must still be drained within the same Pre-Active pass,
// ahead of any Active event.
TEST(PliPreActiveSim, PreActiveCreatedPreActiveEventRunsBeforeActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() {
    order.push_back("pre_active");
    auto* again = sched.GetEventPool().Acquire();
    again->callback = [&order]() { order.push_back("pre_active_created"); };
    sched.ScheduleEvent({0}, Region::kPreActive, again);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "pre_active_created");
  EXPECT_EQ(order[2], "active");
}

// Pre-Active is an unrestricted control point: writing values and creating
// events from within it is explicitly permitted, unlike the read-only Preponed
// and Postponed regions. The scheduler must not flag such activity as illegal.
TEST(PliPreActiveSim, PreActiveWritesAndSchedulingAreNotFlaggedIllegal) {
  Arena arena;
  Scheduler sched(arena);

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() {
    sched.NoteWriteAttempt();
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, ev);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 0u);
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 0u);
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 0u);
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
}

// The "write values ... before events in the Active region are evaluated" facet
// of §4.4.3.2, driven through the real VPI write path rather than the synthetic
// NoteWriteAttempt shortcut used above. A vpi_put_value() issued from a
// Pre-Active PLI callback flows through PutValueApplyWriteAndForce, so it both
// takes effect (an Active-region read via vpi_get_value() sees the new value,
// proving the write landed ahead of the Active region) and is left un-flagged:
// unlike the read-only Preponed/Postponed/Pre-Observed regions, a Pre-Active
// write records no illegal-write violation.
TEST(PliPreActiveSim, VpiPutValueFromPreActiveTakesEffectAndIsNotFlagged) {
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

  auto* pre_active = sched.GetEventPool().Acquire();
  pre_active->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 77;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pre_active);

  int seen_in_active = -1;
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    VpiValue out{};
    out.format = kVpiIntVal;
    vpi.GetValue(&obj, &out);
    seen_in_active = out.value.integer;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();

  EXPECT_EQ(seen_in_active, 77);
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 0u);
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 0u);
  EXPECT_EQ(sched.IllegalPreObservedWriteCount(), 0u);
}
