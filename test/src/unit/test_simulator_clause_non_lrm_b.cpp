// §non_lrm

#include <gtest/gtest.h>

#include <vector>

#include "simulation/mt_sim.h"

using namespace delta;

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

}  // namespace
