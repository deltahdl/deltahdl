// Non-LRM tests

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

namespace {

// --- EventPool tests ---
TEST(EventPool, AcquireCreatesNew) {
  Arena arena;
  EventPool pool(arena);
  Event *ev = pool.Acquire();
  ASSERT_NE(ev, nullptr);
  EXPECT_EQ(ev->kind, EventKind::kEvaluation);
  EXPECT_EQ(ev->target, nullptr);
  EXPECT_EQ(ev->next, nullptr);
}

TEST(EventPool, ReleaseAndReuse) {
  Arena arena;
  EventPool pool(arena);
  Event *ev = pool.Acquire();
  ev->callback = []() {};
  ev->target = reinterpret_cast<void *>(0x1234);
  pool.Release(ev);
  EXPECT_EQ(pool.FreeCount(), 1);

  Event *reused = pool.Acquire();
  EXPECT_EQ(reused, ev);               // Same pointer returned
  EXPECT_EQ(reused->target, nullptr);  // Fields cleared
  EXPECT_EQ(pool.FreeCount(), 0);
}

TEST(EventPool, FreeCount) {
  Arena arena;
  EventPool pool(arena);
  EXPECT_EQ(pool.FreeCount(), 0);

  Event *ev1 = pool.Acquire();
  Event *ev2 = pool.Acquire();
  pool.Release(ev1);
  pool.Release(ev2);
  EXPECT_EQ(pool.FreeCount(), 2);

  pool.Acquire();
  EXPECT_EQ(pool.FreeCount(), 1);
}

TEST(Scheduler, EventPoolIntegration) {
  Arena arena;
  Scheduler sched(arena);
  auto &pool = sched.GetEventPool();
  EXPECT_EQ(pool.FreeCount(), 0);

  auto *ev = pool.Acquire();
  bool ran = false;
  ev->callback = [&ran]() { ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_TRUE(ran);
  // After execution, event should be recycled into the pool.
  EXPECT_EQ(pool.FreeCount(), 1);
}

// Helper fixture for clocking simulation tests.
struct ClockingSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

// Schedule posedge at a given time through the scheduler.
void SchedulePosedge(ClockingSimFixture &f, Variable *clk, uint64_t time) {
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

// Schedule negedge at a given time through the scheduler.
void ScheduleNegedge(ClockingSimFixture &f, Variable *clk, uint64_t time) {
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

// =============================================================================
// EventCoalescer
// =============================================================================
TEST(AdvSim, EventCoalescerMergesDuplicates) {
  EventCoalescer coalescer;
  uint32_t target_id = 42;
  coalescer.Add(target_id, 100);
  coalescer.Add(target_id, 200);
  coalescer.Add(target_id, 300);
  // Only last value for each target should survive.
  auto entries = coalescer.Drain();
  ASSERT_EQ(entries.size(), 1u);
  EXPECT_EQ(entries[0].target_id, target_id);
  EXPECT_EQ(entries[0].value, 300u);
}

TEST(AdvSim, EventCoalescerKeepsDistinctTargets) {
  EventCoalescer coalescer;
  coalescer.Add(1, 10);
  coalescer.Add(2, 20);
  coalescer.Add(3, 30);
  auto entries = coalescer.Drain();
  EXPECT_EQ(entries.size(), 3u);
}

TEST(AdvSim, EventCoalescerDrainClearsState) {
  EventCoalescer coalescer;
  coalescer.Add(1, 10);
  auto first = coalescer.Drain();
  EXPECT_EQ(first.size(), 1u);
  auto second = coalescer.Drain();
  EXPECT_TRUE(second.empty());
}

// =============================================================================
// Partitioner
// =============================================================================
TEST(MtSim, IndependentProcessesSinglePartition) {
  Partitioner part;
  // Process 0 reads "a", writes "b".
  part.AddDependency({0, {"a"}, {"b"}});
  // Process 1 reads "c", writes "d".
  part.AddDependency({1, {"c"}, {"d"}});

  auto partitions = part.BuildPartitions();
  // No conflicts: both should end up in the same partition.
  EXPECT_EQ(partitions.size(), 1u);
  EXPECT_EQ(partitions[0].process_ids.size(), 2u);
}

TEST(MtSim, ConflictingProcessesSeparatePartitions) {
  Partitioner part;
  // Process 0 writes "x".
  part.AddDependency({0, {}, {"x"}});
  // Process 1 reads "x".
  part.AddDependency({1, {"x"}, {}});

  auto partitions = part.BuildPartitions();
  // Write-read conflict: must be in separate partitions.
  EXPECT_EQ(partitions.size(), 2u);
}

TEST(MtSim, WriteWriteConflict) {
  Partitioner part;
  part.AddDependency({0, {}, {"sig"}});
  part.AddDependency({1, {}, {"sig"}});

  auto partitions = part.BuildPartitions();
  EXPECT_EQ(partitions.size(), 2u);
}

TEST(MtSim, EmptyPartitioner) {
  Partitioner part;
  auto partitions = part.BuildPartitions();
  EXPECT_TRUE(partitions.empty());
  EXPECT_EQ(part.ProcessCount(), 0u);
}

}  // namespace
