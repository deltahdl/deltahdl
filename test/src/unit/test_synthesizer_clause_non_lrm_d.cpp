// §non_lrm

#include <gtest/gtest.h>

#include <cstdint>

#include "synthesis/adv_synth.h"
#include "synthesis/aig.h"
#include "synthesis/lut_map.h"

using namespace delta;

namespace {

// =============================================================================
// MapForDelay
// =============================================================================
TEST(AdvSynth, MapForDelayReturnsValidMapping) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto ab = g.AddAnd(a, b);
  auto abc = g.AddAnd(ab, c);
  g.AddOutput(abc);

  uint32_t lut_size = 4;
  auto mapping = MapForDelay(g, lut_size);

  // All cells must respect the LUT size constraint.
  EXPECT_FALSE(mapping.cells.empty());
  for (const auto &cell : mapping.cells) {
    EXPECT_LE(cell.inputs.size(), static_cast<size_t>(lut_size));
  }
  EXPECT_EQ(mapping.lut_size, lut_size);
}

TEST(AdvSynth, MapForDelayHandlesConstantOutput) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstFalse);

  auto mapping = MapForDelay(g, 4);
  ASSERT_EQ(mapping.cells.size(), 1);
  EXPECT_EQ(mapping.cells[0].truth_table, 0u);
}

// =============================================================================
// IterativeAreaDelay
// =============================================================================
TEST(AdvSynth, IterativeAreaDelayConverges) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto d = g.AddInput();
  auto ab = g.AddAnd(a, b);
  auto cd = g.AddAnd(c, d);
  auto abcd = g.AddAnd(ab, cd);
  g.AddOutput(abcd);

  uint32_t lut_size = 4;
  uint32_t iterations = 3;
  auto mapping = IterativeAreaDelay(g, lut_size, iterations);

  // Result must be a valid mapping.
  EXPECT_FALSE(mapping.cells.empty());
  for (const auto &cell : mapping.cells) {
    EXPECT_LE(cell.inputs.size(), static_cast<size_t>(lut_size));
  }
  EXPECT_EQ(mapping.lut_size, lut_size);
}

TEST(AdvSynth, IterativeAreaDelayWithSingleNode) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  auto mapping = IterativeAreaDelay(g, 4, 2);

  EXPECT_FALSE(mapping.cells.empty());
  for (const auto &cell : mapping.cells) {
    EXPECT_LE(cell.inputs.size(), 4u);
  }
}

TEST(AdvSynth, IterativeAreaDelayZeroIterationsReturnsMappingForDelay) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  // Zero iterations should still return a valid mapping (the initial one).
  auto mapping = IterativeAreaDelay(g, 4, 0);
  EXPECT_FALSE(mapping.cells.empty());
}

}  // namespace
