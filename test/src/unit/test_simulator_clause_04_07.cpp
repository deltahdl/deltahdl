#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/scheduler.h"
#include "simulator/stmt_exec.h"

using namespace delta;

namespace {

// §4.7 ¶1 sentence 1: "active events can be taken off the Active or
// Reactive event region and processed in any order". The scheduler
// classifies exactly those two regions as any-order regions; every
// other region is reported as not any-order, so callers can reason
// about where §4.7's latitude applies.
TEST(NondeterminismSim, AnyOrderRegionsAreActiveAndReactive) {
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kActive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kReactive));
  EXPECT_FALSE(Scheduler::IsAnyOrderRegion(Region::kPreponed));
  EXPECT_FALSE(Scheduler::IsAnyOrderRegion(Region::kInactive));
  EXPECT_FALSE(Scheduler::IsAnyOrderRegion(Region::kNBA));
  EXPECT_FALSE(Scheduler::IsAnyOrderRegion(Region::kObserved));
  EXPECT_FALSE(Scheduler::IsAnyOrderRegion(Region::kReNBA));
  EXPECT_FALSE(Scheduler::IsAnyOrderRegion(Region::kPostponed));
}

// §4.7 ¶1 last sentence: "the order of interleaved execution is
// nondeterministic and not under control of the user". The scheduler
// attests this by reporting that no user-facing ordering API exists.
TEST(NondeterminismSim, SchedulerDoesNotAllowUserOrderControl) {
  EXPECT_FALSE(Scheduler::AllowsUserOrderControl());
}

// §4.7 ¶1 sentence 3: "Time control statements are the # expression and
// @ expression constructs (see 9.4)". The stmt-exec classifier marks
// StmtKind::kDelay (the # expression) and StmtKind::kEventControl (the
// @ expression) as time-control, in line with §4.7's definition.
TEST(NondeterminismSim, DelayAndEventControlAreTimeControlStatements) {
  EXPECT_TRUE(IsTimeControlStatement(StmtKind::kDelay));
  EXPECT_TRUE(IsTimeControlStatement(StmtKind::kEventControl));
}

// §4.7 ¶1 sentence 3 (boundary): the classifier rejects every other
// statement kind. §4.7 names only # and @; cycle delay (##N), wait,
// and the generic timing-control wrapper are governed elsewhere and
// must not be folded into the §4.7 definition.
TEST(NondeterminismSim, NonTimeControlStatementsAreClassifiedFalse) {
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kBlockingAssign));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kNonblockingAssign));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kIf));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kFor));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kBlock));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kCycleDelay));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kWait));
  EXPECT_FALSE(IsTimeControlStatement(StmtKind::kTimingControl));
}

// §4.7 ¶1 sentences 2–4 in action: an event simulates the simulator
// suspending evaluation of a procedural statement mid-flight. It
// records the suspension via the scheduler's §4.7 hook, then re-queues
// the remainder of the statement as a pending event in the Active
// region. Between the two halves, an unrelated event from another
// process interleaves — demonstrating the §4.7 effect that
// "interleaving of process execution" is observable.
TEST(NondeterminismSim, MidStatementSuspensionInterleavesAndCounts) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* first_half = sched.GetEventPool().Acquire();
  first_half->callback = [&]() {
    order.push_back("stmtA_part1");
    sched.NoteMidStatementSuspension();
    auto* second_half = sched.GetEventPool().Acquire();
    second_half->callback = [&]() { order.push_back("stmtA_part2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, second_half);
  };
  sched.ScheduleEvent({0}, Region::kActive, first_half);

  auto* other_process = sched.GetEventPool().Acquire();
  other_process->callback = [&]() { order.push_back("stmtB"); };
  sched.ScheduleEvent({0}, Region::kActive, other_process);

  sched.Run();

  std::vector<std::string> expected = {"stmtA_part1", "stmtB", "stmtA_part2"};
  EXPECT_EQ(order, expected);
  EXPECT_EQ(sched.MidStatementSuspensionCount(), 1u);
}

}  // namespace
