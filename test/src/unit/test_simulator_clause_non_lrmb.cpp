// §non_lrm

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/compiled_sim.h"
#include "simulation/mt_sim.h"
#include "simulation/sim_context.h"
#include <atomic>
#include <gtest/gtest.h>
#include <vector>

using namespace delta;

struct MtSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
namespace {

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

// =============================================================================
// MtScheduler
// =============================================================================
TEST(MtSim, MtSchedulerInit) {
  MtScheduler sched(4);
  EXPECT_EQ(sched.NumThreads(), 4u);
  EXPECT_EQ(sched.NumPartitions(), 0u);
}

TEST(MtSim, MtSchedulerSetPartitions) {
  MtScheduler sched(2);
  std::vector<SimPartition> parts;
  parts.push_back({0, {0, 1}});
  parts.push_back({1, {2, 3}});
  sched.SetPartitions(parts);

  EXPECT_EQ(sched.NumPartitions(), 2u);
  EXPECT_EQ(sched.Partitions()[0].process_ids.size(), 2u);
  EXPECT_EQ(sched.Partitions()[1].process_ids.size(), 2u);
}

TEST(MtSim, RunTimestepExecutesProcesses) {
  MtSimFixture f;
  auto *a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto *b = f.ctx.CreateVariable("b", 32);
  b->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Two compiled processes: proc0 sets a=42, proc1 sets b=99.
  std::vector<CompiledProcess> processes;
  processes.emplace_back(0, [](SimContext &ctx) {
    auto *var = ctx.FindVariable("a");
    if (var)
      var->value.words[0].aval = 42;
  });
  processes.emplace_back(1, [](SimContext &ctx) {
    auto *var = ctx.FindVariable("b");
    if (var)
      var->value.words[0].aval = 99;
  });

  // Two independent partitions.
  std::vector<SimPartition> partitions = {{0, {0}}, {1, {1}}};

  MtScheduler sched(2);
  sched.SetPartitions(partitions);
  sched.RunTimestep(f.ctx, processes);

  EXPECT_EQ(a->value.ToUint64(), 42u);
  EXPECT_EQ(b->value.ToUint64(), 99u);
}

TEST(MtSim, RunTimestepEmptyPartitions) {
  MtSimFixture f;
  std::vector<CompiledProcess> processes;
  MtScheduler sched(2);
  sched.RunTimestep(f.ctx, processes);
  // Should not crash.
}

TEST(MtSim, RunTimestepMultipleThreads) {
  MtSimFixture f;

  // Use string literals for stable string_view keys.
  const char *names[] = {"v0", "v1", "v2", "v3"};
  std::vector<Variable *> vars;
  for (int i = 0; i < 4; ++i) {
    auto *var = f.ctx.CreateVariable(names[i], 32);
    var->value = MakeLogic4VecVal(f.arena, 32, 0);
    vars.push_back(var);
  }

  // 4 processes, each incrementing a separate variable.
  std::vector<CompiledProcess> processes;
  processes.reserve(4);
  for (uint32_t i = 0; i < 4; ++i) {
    processes.emplace_back(i, [i, &names](SimContext &ctx) {
      auto *var = ctx.FindVariable(names[i]);
      if (var)
        var->value.words[0].aval += 1;
    });
  }

  // 4 independent partitions.
  std::vector<SimPartition> partitions;
  partitions.reserve(4);
  for (uint32_t i = 0; i < 4; ++i) {
    partitions.push_back({i, {i}});
  }

  MtScheduler sched(4);
  sched.SetPartitions(partitions);
  sched.RunTimestep(f.ctx, processes);

  for (int i = 0; i < 4; ++i) {
    EXPECT_EQ(vars[i]->value.ToUint64(), 1u) << "Variable " << names[i];
  }
}

} // namespace
