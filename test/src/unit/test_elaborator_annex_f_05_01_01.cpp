#include <gtest/gtest.h>

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"

using namespace delta;

namespace {

// The §F.5.1.1 result of clocking a single Boolean: (!c[*0:$] ##1 c & atom).
std::shared_ptr<const SequenceExpr> ClockedBoolean(const char* clock,
                                                   const char* atom) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(BoolAtom(clock)))),
                   SeqBoolean(BoolAnd(BoolAtom(clock), BoolAtom(atom))));
}

// §F.5.1.1: T^s(b, c) = (!c[*0:$] ##1 c & b). The clock may idle, then b is
// sampled on the cycle in which the clock holds.
TEST(SequenceRewrite, BooleanBecomesIdleThenClockedSample) {
  auto result =
      RewriteSequenceUnderClock(*SeqBoolean(BoolAtom("a")), BoolAtom("clk"));
  EXPECT_TRUE(SequenceExprEqual(*result, *ClockedBoolean("clk", "a")));
}

// §F.5.1.1: T^s((1, v = e), c) = (T^s(1, c) ##0 (1, v = e)). The sampled
// assignment fuses onto the clocked tick that the constant 1 rewrites to.
TEST(SequenceRewrite, LocalVarSamplingFusesOntoClockedOne) {
  auto result =
      RewriteSequenceUnderClock(*SeqLocalVarSampling("v"), BoolAtom("clk"));
  auto clocked_one =
      SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(BoolAtom("clk")))),
                SeqBoolean(BoolAnd(BoolAtom("clk"), BoolTrue())));
  auto expected = SeqFusion(clocked_one, SeqLocalVarSampling("v"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((@(c2) r), c1) = T^s(r, c2). The inner clock c2 takes over and
// the incoming clock c1 is discarded.
TEST(SequenceRewrite, NestedClockSupersedesIncomingClock) {
  auto inner_clocked = SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*inner_clocked, BoolAtom("c1"));
  EXPECT_TRUE(SequenceExprEqual(*result, *ClockedBoolean("c2", "a")));
}

// §F.5.1.1: T^s((r1 ##1 r2), c) distributes the clock through concatenation.
TEST(SequenceRewrite, ConcatenationDistributesClock) {
  auto input = SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected =
      SeqConcat(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((r1 ##0 r2), c) distributes the clock through fusion.
TEST(SequenceRewrite, FusionDistributesClock) {
  auto input = SeqFusion(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected =
      SeqFusion(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((r1 or r2), c) distributes the clock through or.
TEST(SequenceRewrite, OrDistributesClock) {
  auto input = SeqOr(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqOr(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((r1 intersect r2), c) distributes the clock through intersect.
TEST(SequenceRewrite, IntersectDistributesClock) {
  auto input =
      SeqIntersect(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected =
      SeqIntersect(ClockedBoolean("clk", "a"), ClockedBoolean("clk", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((first_match(r)), c) = (first_match(T^s(r, c))).
TEST(SequenceRewrite, FirstMatchWrapsClockedBody) {
  auto input = SeqFirstMatch(SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqFirstMatch(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((r[*0]), c) = (T^s(r, c)[*0]).
TEST(SequenceRewrite, NullRepetitionWrapsClockedBody) {
  auto input = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqNullRepeat(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: T^s((r[*1:$]), c) = (T^s(r, c)[*1:$]).
TEST(SequenceRewrite, UnboundedRepetitionWrapsClockedBody) {
  auto input = SeqUnboundedRepeat(SeqBoolean(BoolAtom("a")));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("clk"));
  auto expected = SeqUnboundedRepeat(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

// §F.5.1.1: distribution and the nested-clock rule combine -- in
// (a ##1 @(c2) b) the left operand keeps the outer clock c1 while the right
// operand picks up its own inner clock c2.
TEST(SequenceRewrite, DistributionHonorsPerOperandClock) {
  auto input = SeqConcat(SeqBoolean(BoolAtom("a")),
                         SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("b"))));
  auto result = RewriteSequenceUnderClock(*input, BoolAtom("c1"));
  auto expected =
      SeqConcat(ClockedBoolean("c1", "a"), ClockedBoolean("c2", "b"));
  EXPECT_TRUE(SequenceExprEqual(*result, *expected));
}

}  // namespace
