#include <gtest/gtest.h>

#include <cstdint>

#include "synthesizer/adv_synth.h"
#include "synthesizer/aig.h"
#include "synthesizer/lut_map.h"

using namespace delta;

namespace {

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

  EXPECT_EQ(cell.truth_table, 0b1000u);
}

TEST(LutMap, NotGateMapsToOneLut) {
  AigGraph g;
  auto a = g.AddInput();
  auto not_a = g.AddNot(a);
  g.AddOutput(not_a);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  const auto& cell = mapping.cells[0];

  EXPECT_EQ(cell.inputs.size(), 1u);
  EXPECT_EQ(cell.truth_table, 0b01u);
}

TEST(LutMap, DirectWireMapsToOneLut) {
  AigGraph g;
  auto a = g.AddInput();
  g.AddOutput(a);

  LutMapper mapper(4);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.cells.size(), 1);
  const auto& cell = mapping.cells[0];

  EXPECT_EQ(cell.inputs.size(), 1u);
  EXPECT_EQ(cell.truth_table, 0b10u);
}

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

  EXPECT_EQ(mapping.cells[0].output, AigVar(c));

  EXPECT_EQ(mapping.cells[1].output, AigVar(d));
}

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

TEST(LutMap, LutSizeParameterIsRespected) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto ab = g.AddAnd(a, b);
  auto abc = g.AddAnd(ab, c);
  g.AddOutput(abc);

  LutMapper mapper2(2);
  auto mapping2 = mapper2.Map(g);

  for (const auto& cell : mapping2.cells) {
    EXPECT_LE(cell.inputs.size(), 2u);
  }

  LutMapper mapper4(4);
  auto mapping4 = mapper4.Map(g);

  EXPECT_GE(mapping4.cells.size(), 1u);
  for (const auto& cell : mapping4.cells) {
    EXPECT_LE(cell.inputs.size(), 4u);
  }
}

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

  uint32_t popcount = 0;
  uint64_t tt = cell.truth_table;
  while (tt != 0) {
    popcount += tt & 1u;
    tt >>= 1;
  }
  EXPECT_EQ(popcount, 3u);
}

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

  EXPECT_FALSE(mapping.cells.empty());
  for (const auto& cell : mapping.cells) {
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

  EXPECT_FALSE(mapping.cells.empty());
  for (const auto& cell : mapping.cells) {
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
  for (const auto& cell : mapping.cells) {
    EXPECT_LE(cell.inputs.size(), 4u);
  }
}

TEST(AdvSynth, IterativeAreaDelayZeroIterationsReturnsMappingForDelay) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  auto mapping = IterativeAreaDelay(g, 4, 0);
  EXPECT_FALSE(mapping.cells.empty());
}

}
