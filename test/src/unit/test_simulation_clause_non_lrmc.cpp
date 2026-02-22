// §non_lrm

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include "common/arena.h"
#include "common/types.h"
#include "simulation/adv_sim.h"

using namespace delta;

namespace {

// =============================================================================
// TwoStateDetector
// =============================================================================
TEST(AdvSim, TwoStateDetectorKnown2State) {
  Arena arena;
  auto vec = MakeLogic4VecVal(arena, 8, 0x42);
  EXPECT_TRUE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorWith4StateValue) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 8);
  // Set bval to non-zero to indicate X/Z.
  vec.words[0].bval = 0x01;
  EXPECT_FALSE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorZeroWidth) {
  Logic4Vec empty;
  empty.width = 0;
  empty.nwords = 0;
  empty.words = nullptr;
  EXPECT_TRUE(TwoStateDetector::Is2State(empty));
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

}  // namespace
