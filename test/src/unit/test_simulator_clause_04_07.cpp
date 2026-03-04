#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh47, ActiveRegionProcessesAllEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh47, ReactiveRegionProcessesAllEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh47, IndependentActiveProcessesInterleave) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;

  auto* ev_a = sched.GetEventPool().Acquire();
  ev_a->callback = [&]() { a = 1; };
  sched.ScheduleEvent({0}, Region::kActive, ev_a);

  auto* ev_b = sched.GetEventPool().Acquire();
  ev_b->callback = [&]() { b = 2; };
  sched.ScheduleEvent({0}, Region::kActive, ev_b);

  sched.Run();

  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
}

TEST(SimCh47, IndependentReactiveProcessesInterleave) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;

  auto* ev_a = sched.GetEventPool().Acquire();
  ev_a->callback = [&]() { a = 10; };
  sched.ScheduleEvent({0}, Region::kReactive, ev_a);

  auto* ev_b = sched.GetEventPool().Acquire();
  ev_b->callback = [&]() { b = 20; };
  sched.ScheduleEvent({0}, Region::kReactive, ev_b);

  sched.Run();
  EXPECT_EQ(a, 10);
  EXPECT_EQ(b, 20);
}

TEST(SimCh47, ProcessSuspensionViaPendingEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* a_part1 = sched.GetEventPool().Acquire();
  a_part1->callback = [&]() {
    order.push_back("A_part1");
    auto* a_part2 = sched.GetEventPool().Acquire();
    a_part2->callback = [&]() { order.push_back("A_part2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, a_part2);
  };
  sched.ScheduleEvent({0}, Region::kActive, a_part1);

  auto* b = sched.GetEventPool().Acquire();
  b->callback = [&]() { order.push_back("B"); };
  sched.ScheduleEvent({0}, Region::kActive, b);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "A_part1");
  EXPECT_EQ(order[1], "B");

  EXPECT_EQ(order[2], "A_part2");
}

TEST(SimCh47, MultipleProcessInterleaving) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() {
    order.push_back("A1");
    auto* a2 = sched.GetEventPool().Acquire();
    a2->callback = [&]() { order.push_back("A2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, a2);
  };
  sched.ScheduleEvent({0}, Region::kActive, a1);

  auto* b = sched.GetEventPool().Acquire();
  b->callback = [&]() { order.push_back("B"); };
  sched.ScheduleEvent({0}, Region::kActive, b);

  auto* c1 = sched.GetEventPool().Acquire();
  c1->callback = [&]() {
    order.push_back("C1");
    auto* c2 = sched.GetEventPool().Acquire();
    c2->callback = [&]() { order.push_back("C2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, c2);
  };
  sched.ScheduleEvent({0}, Region::kActive, c1);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);

  EXPECT_EQ(order[0], "A1");
  EXPECT_EQ(order[1], "B");
  EXPECT_EQ(order[2], "C1");

  EXPECT_EQ(order[3], "A2");
  EXPECT_EQ(order[4], "C2");
}

TEST(SimCh47, ConflictingWritesInActiveRegion) {
  Arena arena;
  Scheduler sched(arena);
  int x = 0;

  auto* ev1 = sched.GetEventPool().Acquire();
  ev1->callback = [&]() { x = 10; };
  sched.ScheduleEvent({0}, Region::kActive, ev1);

  auto* ev2 = sched.GetEventPool().Acquire();
  ev2->callback = [&]() { x = 20; };
  sched.ScheduleEvent({0}, Region::kActive, ev2);

  sched.Run();

  EXPECT_TRUE(x == 10 || x == 20);
}

TEST(SimCh47, DynamicallyGeneratedActiveEventsExecute) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* gen = sched.GetEventPool().Acquire();
  gen->callback = [&]() {
    order.push_back(0);
    for (int i = 1; i <= 3; ++i) {
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = [&order, i]() { order.push_back(i); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, gen);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], 0);

  EXPECT_EQ(order[1], 1);
  EXPECT_EQ(order[2], 2);
  EXPECT_EQ(order[3], 3);
}

TEST(SimCh47, ReactiveProcessSuspensionViaReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() {
    order.push_back("RA1");
    auto* a2 = sched.GetEventPool().Acquire();
    a2->callback = [&]() { order.push_back("RA2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReInactive, a2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, a1);

  auto* b = sched.GetEventPool().Acquire();
  b->callback = [&]() { order.push_back("RB"); };
  sched.ScheduleEvent({0}, Region::kReactive, b);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "RA1");
  EXPECT_EQ(order[1], "RB");

  EXPECT_EQ(order[2], "RA2");
}

TEST(SimCh47, NondeterminismAcrossTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* t0a = sched.GetEventPool().Acquire();
  t0a->callback = [&]() { order.push_back("t0_a"); };
  sched.ScheduleEvent({0}, Region::kActive, t0a);

  auto* t0b = sched.GetEventPool().Acquire();
  t0b->callback = [&]() { order.push_back("t0_b"); };
  sched.ScheduleEvent({0}, Region::kActive, t0b);

  auto* t5a = sched.GetEventPool().Acquire();
  t5a->callback = [&]() { order.push_back("t5_a"); };
  sched.ScheduleEvent({5}, Region::kActive, t5a);

  auto* t5b = sched.GetEventPool().Acquire();
  t5b->callback = [&]() { order.push_back("t5_b"); };
  sched.ScheduleEvent({5}, Region::kActive, t5b);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  std::vector<std::string> t0(order.begin(), order.begin() + 2);
  std::sort(t0.begin(), t0.end());
  EXPECT_EQ(t0, (std::vector<std::string>{"t0_a", "t0_b"}));

  std::vector<std::string> t5(order.begin() + 2, order.end());
  std::sort(t5.begin(), t5.end());
  EXPECT_EQ(t5, (std::vector<std::string>{"t5_a", "t5_b"}));
}
