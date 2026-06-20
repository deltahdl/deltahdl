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

TEST(PliPreponedSim, ScheduleFromActiveIntoOtherRegionIsNotFlagged) {
  VerifyScheduleFromActiveIsNotFlagged(
      [](Scheduler& s) { return s.IllegalPreponedScheduleCount(); });
}

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

TEST(PliPreponedSim, MultipleIllegalWritesAreEachCounted) {
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
    for (int i = 0; i < 4; ++i) {
      VpiValue value{};
      value.format = kVpiIntVal;
      value.value.integer = i;
      vpi.PutValue(&obj, &value, nullptr, 0);
    }
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 4u);
}

TEST(PliPreponedSim, VpiPutValueOutsidePreponedDoesNotRecordViolation) {
  VerifyVpiWriteFromActiveIsNotFlagged(
      [](Scheduler& s) { return s.IllegalPreponedWriteCount(); });
}

TEST(PliPreponedSim,
     IllegalScheduleIntoEveryNonPreponedRegionAtCurrentTimeIsFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    for (size_t i = 0; i < kRegionCount; ++i) {
      auto r = static_cast<Region>(i);
      if (r == Region::kPreponed) continue;
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = []() {};
      sched.ScheduleEvent(sched.CurrentTime(), r, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), kRegionCount - 1);
}

TEST(PliPreponedSim,
     WriteAndScheduleViolationsFromPreponedAreCountedIndependently) {
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
    auto* offender = sched.GetEventPool().Acquire();
    offender->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, offender);

    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 7;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedScheduleCount(), 1u);
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 1u);
}

TEST(PliPreponedSim, VpiPutValueOnNetFromPreponedRecordsWriteViolation) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Net net{};
  VpiObject obj{};
  obj.net = &net;

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 1;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPreponedWriteCount(), 1u);
}
