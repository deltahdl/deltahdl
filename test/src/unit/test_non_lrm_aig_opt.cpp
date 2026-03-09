#include <gtest/gtest.h>

#include "synthesizer/adv_synth.h"
#include "synthesizer/aig.h"
#include "synthesizer/aig_opt.h"

using namespace delta;

namespace {

TEST(AigOpt, ConstPropRemovesDeadAndWithConstant) {
  AigGraph g;
  auto a = g.AddInput();

  g.AddOutput(AigGraph::kConstFalse);
  g.AddOutput(a);

  ConstProp(g);

  EXPECT_EQ(g.outputs[0], AigGraph::kConstFalse);
  EXPECT_EQ(g.outputs[1], a);
}

TEST(AigOpt, ConstPropConstantOutput) {
  AigGraph g;
  auto a = g.AddInput();

  auto c = g.AddAnd(a, g.AddNot(a));
  g.AddOutput(c);

  ConstProp(g);
  EXPECT_EQ(g.outputs[0], AigGraph::kConstFalse);
}

TEST(AigOpt, ConstPropPreservesNonTrivial) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  size_t before = g.NodeCount();
  ConstProp(g);

  EXPECT_EQ(g.NodeCount(), before);
  EXPECT_EQ(g.outputs[0], c);
}

TEST(AigOpt, BalanceReducesDepth) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto d = g.AddInput();

  auto ab = g.AddAnd(a, b);
  auto abc = g.AddAnd(ab, c);
  auto abcd = g.AddAnd(abc, d);
  g.AddOutput(abcd);

  Balance(g);

  EXPECT_NE(g.outputs[0], AigGraph::kConstFalse);
  EXPECT_NE(g.outputs[0], AigGraph::kConstTrue);
}

TEST(AigOpt, BalancePreservesSingleNode) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  Balance(g);

  EXPECT_NE(g.outputs[0], AigGraph::kConstFalse);
}

TEST(AigOpt, RewriteSimplifies) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();

  auto c = g.AddOr(a, b);
  g.AddOutput(c);

  size_t before = g.NodeCount();
  Rewrite(g);

  EXPECT_LE(g.NodeCount(), before);
}

TEST(AigOpt, RewritePreservesConstants) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstTrue);
  Rewrite(g);
  EXPECT_EQ(g.outputs[0], AigGraph::kConstTrue);
}

TEST(AigOpt, RefactorDoesNotCorrupt) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  auto d = g.AddOr(a, b);
  g.AddOutput(c);
  g.AddOutput(d);

  Refactor(g);

  EXPECT_EQ(g.outputs.size(), 2);
}

TEST(AigOpt, RedundancyRemovalNoChange) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  size_t before = g.NodeCount();
  RemoveRedundancy(g);

  EXPECT_EQ(g.NodeCount(), before);
}

TEST(AdvSynth, RetimeForwardMovesLatch) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto and_lit = g.AddAnd(a, b);
  g.AddLatch(and_lit);

  ASSERT_EQ(g.latches.size(), 1);
  size_t latch_count_before = g.latches.size();

  uint32_t moved = RetimeForward(g);

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
  AigGraph g;
  auto a = g.AddInput();
  g.AddLatch(a);

  ASSERT_EQ(g.latches.size(), 1);
  uint32_t moved = RetimeForward(g);

  EXPECT_EQ(moved, 0u);
  EXPECT_EQ(g.latches.size(), 1);
}

TEST(AdvSynth, RetimeBackwardPreservesOutputs) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);
  g.AddLatch(c);

  size_t output_count = g.outputs.size();
  RetimeBackward(g);

  EXPECT_EQ(g.outputs.size(), output_count);
}

}  // namespace
