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

TEST(NondeterminismSim, SchedulerDoesNotAllowUserOrderControl) {
  EXPECT_FALSE(Scheduler::AllowsUserOrderControl());
}

TEST(NondeterminismSim, DelayAndEventControlAreTimeControlStatements) {
  EXPECT_TRUE(IsTimeControlStatement(StmtKind::kDelay));
  EXPECT_TRUE(IsTimeControlStatement(StmtKind::kEventControl));
}

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
