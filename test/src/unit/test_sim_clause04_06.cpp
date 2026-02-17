#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.6 Determinism
//
// LRM §4.6:
//   "This standard guarantees a certain scheduling order:
//    a) Statements within a begin-end block shall be executed in the order
//       in which they appear in that begin-end block. Execution of statements
//       in a particular begin-end block can be suspended in favor of other
//       processes in the model; however, in no case shall the statements in
//       a begin-end block be executed in any order other than that in which
//       they appear in the source.
//    b) NBAs shall be performed in the order the statements were executed
//       (see 10.4.2)."
//
// The LRM example:
//   module test;
//   logic a;
//   initial begin
//     a <= 0;
//     a <= 1;
//   end
//   endmodule
//
// "When this block is executed, there will be two events added to the NBA
// region. ... This rule requires that they be taken from the NBA region and
// performed in execution order as well. Hence, at the end of simulation
// time 0, the variable a will be assigned 0 and then 1."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.6(a) "Statements within a begin-end block shall be executed in the
// order in which they appear"
// Sequential events scheduled in the Active region execute in FIFO order.
// ---------------------------------------------------------------------------
TEST(SimCh46, SequentialStatementsExecuteInSourceOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // Simulate a begin-end block: three sequential statements.
  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], 0);
  EXPECT_EQ(order[1], 1);
  EXPECT_EQ(order[2], 2);
}

// ---------------------------------------------------------------------------
// §4.6(a) "Execution of statements in a particular begin-end block can be
// suspended in favor of other processes"
// A suspended process resumes in order — events from different processes
// interleave but each individual process's events remain in source order.
// ---------------------------------------------------------------------------
TEST(SimCh46, SuspendedProcessResumesInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Process A: stmt0, then suspends (schedules stmt2 in Inactive).
  auto* a0 = sched.GetEventPool().Acquire();
  a0->callback = [&]() {
    order.push_back("A0");
    // A suspends: schedules continuation in Inactive region.
    auto* a1 = sched.GetEventPool().Acquire();
    a1->callback = [&]() { order.push_back("A1"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, a1);
  };
  sched.ScheduleEvent({0}, Region::kActive, a0);

  // Process B: runs while A is suspended.
  auto* b0 = sched.GetEventPool().Acquire();
  b0->callback = [&]() { order.push_back("B0"); };
  sched.ScheduleEvent({0}, Region::kActive, b0);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "A0");
  EXPECT_EQ(order[1], "B0");
  // A resumes after Inactive → Active iteration.
  EXPECT_EQ(order[2], "A1");
}

// ---------------------------------------------------------------------------
// §4.6(a) "in no case shall the statements in a begin-end block be executed
// in any order other than that in which they appear in the source"
// Even with many events, source order (FIFO) is preserved within a region.
// ---------------------------------------------------------------------------
TEST(SimCh46, LargeSequentialBlockPreservesOrder) {
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

// ---------------------------------------------------------------------------
// §4.6(b) "NBAs shall be performed in the order the statements were
// executed"
// Multiple NBA events scheduled in execution order execute in that order.
// ---------------------------------------------------------------------------
TEST(SimCh46, NBAExecutionOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> nba_order;

  // Simulate: a <= 0; a <= 1; a <= 2; (three NBAs in execution order).
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

// ---------------------------------------------------------------------------
// §4.6(b) LRM example: "a <= 0; a <= 1;"
// "Hence, at the end of simulation time 0, the variable a will be assigned
// 0 and then 1."
// The last NBA wins — variable ends up with value 1.
// ---------------------------------------------------------------------------
TEST(SimCh46, NBALastAssignmentWins) {
  Arena arena;
  Scheduler sched(arena);
  int a = -1;

  // a <= 0;
  auto* nba0 = sched.GetEventPool().Acquire();
  nba0->callback = [&]() { a = 0; };
  sched.ScheduleEvent({0}, Region::kNBA, nba0);

  // a <= 1;
  auto* nba1 = sched.GetEventPool().Acquire();
  nba1->callback = [&]() { a = 1; };
  sched.ScheduleEvent({0}, Region::kNBA, nba1);

  sched.Run();
  EXPECT_EQ(a, 1);
}

// ---------------------------------------------------------------------------
// §4.6(b) "two events added to the NBA region ... entered in the event
// region in execution order"
// Active region generates NBAs; they execute in the order they were created.
// ---------------------------------------------------------------------------
TEST(SimCh46, ActiveGeneratedNBAsExecuteInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> nba_order;

  // An Active callback generates three NBAs.
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

// ---------------------------------------------------------------------------
// §4.6(a)+(b) Combined: sequential statements produce NBAs in order, and
// the NBAs also execute in that same order.
// ---------------------------------------------------------------------------
TEST(SimCh46, SequentialStatementsProduceOrderedNBAs) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> log;

  // Simulate a begin-end block with three sequential NBA assignments.
  // Each Active event represents a statement; it creates an NBA.
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
  ASSERT_EQ(log.size(), 6u);
  // Statements execute in order.
  EXPECT_EQ(log[0], "stmt0");
  EXPECT_EQ(log[1], "stmt1");
  EXPECT_EQ(log[2], "stmt2");
  // NBAs execute in execution order (same as statement order).
  EXPECT_EQ(log[3], "nba0");
  EXPECT_EQ(log[4], "nba1");
  EXPECT_EQ(log[5], "nba2");
}

// ---------------------------------------------------------------------------
// §4.6(a) Source-order preservation across multiple time slots.
// Each time slot's begin-end block maintains its own source order.
// ---------------------------------------------------------------------------
TEST(SimCh46, SourceOrderPreservedAcrossTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Time 0: two statements.
  for (int i = 0; i < 2; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("t0_" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  // Time 5: two statements.
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

// ---------------------------------------------------------------------------
// §4.6(b) NBA ordering across time slots.
// NBAs at time 0 execute in order; NBAs at time 5 execute in order.
// ---------------------------------------------------------------------------
TEST(SimCh46, NBAOrderingAcrossTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> values;
  int a = -1;

  // Time 0: a <= 10; a <= 20;
  auto* nba0a = sched.GetEventPool().Acquire();
  nba0a->callback = [&]() { a = 10; };
  sched.ScheduleEvent({0}, Region::kNBA, nba0a);

  auto* nba0b = sched.GetEventPool().Acquire();
  nba0b->callback = [&]() { a = 20; };
  sched.ScheduleEvent({0}, Region::kNBA, nba0b);

  // Postponed at time 0 samples the value after NBA.
  auto* sample0 = sched.GetEventPool().Acquire();
  sample0->callback = [&]() { values.push_back(a); };
  sched.ScheduleEvent({0}, Region::kPostponed, sample0);

  // Time 5: a <= 30; a <= 40;
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
  EXPECT_EQ(values[0], 20);  // Last NBA at time 0 wins.
  EXPECT_EQ(values[1], 40);  // Last NBA at time 5 wins.
}

// ---------------------------------------------------------------------------
// §4.6(b) "performed in execution order" — Reactive region NBAs (Re-NBA)
// also maintain FIFO execution order.
// ---------------------------------------------------------------------------
TEST(SimCh46, ReactiveNBAExecutionOrder) {
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
