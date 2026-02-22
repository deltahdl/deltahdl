// §non_lrm

#include <gtest/gtest.h>

#include <cstdint>

#include "synthesis/adv_synth.h"
#include "synthesis/aig.h"
#include "synthesis/lut_map.h"

using namespace delta;

namespace {

// =============================================================================
// RetimeForward
// =============================================================================
TEST(AdvSynth, RetimeForwardMovesLatch) {
  // Build: two inputs a, b. AND(a, b) feeds a latch next-state.
  // RetimeForward should detect the AND node and split into two latches.
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto and_lit = g.AddAnd(a, b);
  g.AddLatch(and_lit);

  // Before: 1 latch.
  ASSERT_EQ(g.latches.size(), 1);
  size_t latch_count_before = g.latches.size();

  uint32_t moved = RetimeForward(g);

  // The latch should have been split: 1 old latch -> 2 new latches.
  EXPECT_GT(moved, 0u);
  EXPECT_GT(g.latches.size(), latch_count_before);
}

TEST(AdvSynth, RetimeForwardNoOpWhenNoLatches) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  uint32_t moved = RetimeForward(g);
  EXPECT_EQ(moved, 0u);
  EXPECT_TRUE(g.latches.empty());
}

TEST(AdvSynth, RetimeForwardSkipsNonAndNextState) {
  // Latch whose next-state is a direct primary input (not an AND node).
  AigGraph g;
  auto a = g.AddInput();
  g.AddLatch(a);

  ASSERT_EQ(g.latches.size(), 1);
  uint32_t moved = RetimeForward(g);

  // No AND to absorb, so no movement.
  EXPECT_EQ(moved, 0u);
  EXPECT_EQ(g.latches.size(), 1);
}

// =============================================================================
// RetimeBackward
// =============================================================================
TEST(AdvSynth, RetimeBackwardPreservesOutputs) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);
  g.AddLatch(c);

  size_t output_count = g.outputs.size();
  RetimeBackward(g);

  // Outputs must still exist and count should not change.
  EXPECT_EQ(g.outputs.size(), output_count);
}

}  // namespace
