#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

// §4.7 atom 1: within-region drain order is unspecified, so two writes that
// race in the Active region can resolve to either value. The test asserts the
// permitted disjunction rather than a fixed order; production code applies the
// rule by drainpath (FIFO is one valid choice, not a normative requirement).
TEST(NondeterminismSim, ConflictingWritesInActiveRegion) {
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

// §4.7 atom 3: a process under evaluation may be suspended and its remainder
// placed as a pending event. Here A is split into A_part1 and A_part2 by
// scheduling A_part2 into the Inactive sub-region from inside A_part1; B
// runs in between, observing the resulting interleave (atom 4).
TEST(NondeterminismSim, ProcessSuspensionViaPendingEvent) {
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

// §4.7 atom 1 in the active region: schedule N events into Active and
// assert the sorted result, encoding "any permutation is valid" rather
// than locking the test to whichever drain order the implementation
// happens to produce. The production code complies by drainpath without
// imposing a normative ordering between events.
TEST(NondeterminismSim, ActiveEventsProcessedInAnyValidOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 4; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  std::vector<int> sorted = order;
  std::sort(sorted.begin(), sorted.end());
  EXPECT_EQ(sorted, (std::vector<int>{0, 1, 2, 3}));
}

// §4.7 atom 1 in the reactive region: the LRM names Active and Reactive
// in the same sentence, so the same drain-order freedom applies in the
// reactive set. Four events drained in any permutation satisfy the rule.
TEST(NondeterminismSim, ReactiveEventsProcessedInAnyValidOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 4; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  std::vector<int> sorted = order;
  std::sort(sorted.begin(), sorted.end());
  EXPECT_EQ(sorted, (std::vector<int>{0, 1, 2, 3}));
}

// §4.7 atom 3 in the reactive set: suspension uses Re-Inactive as the
// pending sub-region instead of Inactive, but the same atom holds — a
// procedural statement evaluation may be paused and resumed via a pending
// event scheduled into the same region set.
TEST(NondeterminismSim, ReactiveProcessSuspensionViaReInactive) {
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
