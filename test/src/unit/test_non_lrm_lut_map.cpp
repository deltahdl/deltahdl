// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include "synthesis/aig.h"
#include "synthesis/lut_map.h"

using namespace delta;

namespace {

// =============================================================================
// Single AND gate -> single LUT
// =============================================================================
TEST(LutMap, SingleAndGateMapsToOneLut) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  const auto& cell = mapping.cells[0];
  EXPECT_EQ(cell.output, AigVar(c));
  EXPECT_LE(cell.inputs.size(), 4u);

  // AND truth table for 2 inputs: row 0b11 = 1, rest = 0 -> 0b1000 = 8.
  EXPECT_EQ(cell.truth_table, 0b1000u);
}

// =============================================================================
// NOT gate (inverted input to output) -> single LUT
// =============================================================================
TEST(LutMap, NotGateMapsToOneLut) {
  AigGraph g;
  auto a = g.AddInput();
  auto not_a = g.AddNot(a);
  g.AddOutput(not_a);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  const auto& cell = mapping.cells[0];

  // 1-input inverter: truth table 0b01 (output=1 when input=0).
  EXPECT_EQ(cell.inputs.size(), 1u);
  EXPECT_EQ(cell.truth_table, 0b01u);
}

// =============================================================================
// Direct wire (input passed to output) -> single LUT
// =============================================================================
TEST(LutMap, DirectWireMapsToOneLut) {
  AigGraph g;
  auto a = g.AddInput();
  g.AddOutput(a);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  const auto& cell = mapping.cells[0];

  // 1-input identity buffer: truth table 0b10.
  EXPECT_EQ(cell.inputs.size(), 1u);
  EXPECT_EQ(cell.truth_table, 0b10u);
}

// =============================================================================
// Multiple outputs -> multiple LUTs
// =============================================================================
TEST(LutMap, MultipleOutputsProduceMultipleLuts) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  auto d = g.AddOr(a, b);
  g.AddOutput(c);
  g.AddOutput(d);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  EXPECT_EQ(mapping.cells.size(), 2u);

  // First output: AND.
  EXPECT_EQ(mapping.cells[0].output, AigVar(c));
  // Second output: OR.
  EXPECT_EQ(mapping.cells[1].output, AigVar(d));
}

// =============================================================================
// Constant output -> trivial LUT
// =============================================================================
TEST(LutMap, ConstantFalseOutputProducesTrivialLut) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstFalse);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  EXPECT_EQ(mapping.cells[0].truth_table, 0u);
  EXPECT_TRUE(mapping.cells[0].inputs.empty());
}

TEST(LutMap, ConstantTrueOutputProducesTrivialLut) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstTrue);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  EXPECT_EQ(mapping.cells[0].truth_table, 1u);
  EXPECT_TRUE(mapping.cells[0].inputs.empty());
}

// =============================================================================
// LUT size parameter is respected
// =============================================================================
TEST(LutMap, LutSizeParameterIsRespected) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto ab = g.AddAnd(a, b);
  auto abc = g.AddAnd(ab, c);
  g.AddOutput(abc);

  // Map with K=2: LUTs should have at most 2 inputs each.
  LutMapper mapper2(2);
  auto mapping2 = mapper2.Map(g);

  for (const auto& cell : mapping2.cells) {
    EXPECT_LE(cell.inputs.size(), 2u);
  }

  // Map with K=4: can fit in a single LUT.
  LutMapper mapper4(4);
  auto mapping4 = mapper4.Map(g);

  EXPECT_GE(mapping4.cells.size(), 1u);
  for (const auto& cell : mapping4.cells) {
    EXPECT_LE(cell.inputs.size(), 4u);
  }
}

// =============================================================================
// OR gate truth table correctness
// =============================================================================
TEST(LutMap, OrGateTruthTable) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddOr(a, b);
  g.AddOutput(c);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  const auto& cell = mapping.cells[0];

  // OR truth table for 2 inputs: 0|0=0, 0|1=1, 1|0=1, 1|1=1 -> 0b1110 = 14.
  // However, the leaf ordering matters. Check that exactly 3 of 4 rows are 1.
  uint32_t popcount = 0;
  uint64_t tt = cell.truth_table;
  while (tt != 0) {
    popcount += tt & 1u;
    tt >>= 1;
  }
  EXPECT_EQ(popcount, 3u);
}

}  // namespace
