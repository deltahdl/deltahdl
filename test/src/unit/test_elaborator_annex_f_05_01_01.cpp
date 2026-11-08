#include <gtest/gtest.h>

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"

using namespace delta;

namespace {

std::shared_ptr<const SequenceExpr> ClockedBoolean(const char* clock,
                                                   const char* atom) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(BoolAtom(clock)))),
                   SeqBoolean(BoolAnd(BoolAtom(clock), BoolAtom(atom))));
}

TEST(SequenceRewrite, BooleanBecomesIdleThenClockedSample) {
  auto result =
      RewriteSequenceUnderClock(*SeqBoolean(BoolAtom("a")), BoolAtom("clk"));
  EXPECT_TRUE(SequenceExprEqual(*result, *ClockedBoolean("clk", "a")));
}

TEST(SequenceRewrite, LocalVarSamplingFusesOntoClockedOne) {
  auto result =
      RewriteSequenceUnderClock(*SeqLocalVarSampling("v"), BoolAtom("clk"));
  auto clocked_one =
      SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(BoolAtom("clk")))),
                SeqBoolean(BoolAnd(BoolAtom("clk"), BoolTrue())));
  auto expected = SeqFusion(clocked_one, SeqLocalVarSampling("v"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, NestedClockSupersedesIncomingClock) {
  auto inner_clocked = SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*inner_clocked, BoolAtom("c1"));
  EXPECT_TRUE(SequenceExprEqual(*result, *ClockedBoolean("c2", "a")));
}

TEST(SequenceRewrite, ConcatenationDistributesClock) {
  auto input = SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected =
      SeqConcat(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, FusionDistributesClock) {
  auto input = SeqFusion(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected =
      SeqFusion(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, OrDistributesClock) {
  auto input = SeqOr(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqOr(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, IntersectDistributesClock) {
  auto input =
      SeqIntersect(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected =
      SeqIntersect(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, FirstMatchWrapsClockedBody) {
  auto input = SeqFirstMatch(SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqFirstMatch(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, NullRepetitionWrapsClockedBody) {
  auto input = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqNullRepeat(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, UnboundedRepetitionWrapsClockedBody) {
  auto input = SeqUnboundedRepeat(SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqUnboundedRepeat(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

TEST(SequenceRewrite, DistributionHonorsPerOperandClock) {
  auto input = SeqConcat(SeqBoolean(BoolAtom("a")),
                         SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("b"))));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("c1"));
  auto expected =
      SeqConcat(ClockedBoolean("c1", "a"), ClockedBoolean("c2", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

}  // namespace
