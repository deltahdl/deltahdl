#include <gtest/gtest.h>

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_property_rewrite.h"

using namespace delta;

namespace {

std::shared_ptr<const SequenceExpr> ClockedBoolean(const char* clock,
                                                   const char* atom) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(BoolAtom(clock)))),
                   SeqBoolean(BoolAnd(BoolAtom(clock), BoolAtom(atom))));
}

TEST(PropertyClockRewrite, StrongDelegatesToSequenceRewrite) {
  auto input = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkStrong(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, WeakDelegatesToSequenceRewrite) {
  auto input = ClkWeak(SeqBoolean(BoolAtom("a")));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkWeak(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, NestedClockSupersedesIncomingClock) {
  auto input = ClkClock(BoolAtom("c2"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("c1"));
  auto expected = ClkStrong(ClockedBoolean("c2", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, DisableIffPreservesConditionAndClocksBody) {
  auto input =
      ClkDisableIff(BoolAtom("rst"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected =
      ClkDisableIff(BoolAtom("rst"), ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, AcceptOnLeavesConditionUntouched) {
  auto input =
      ClkAcceptOn(BoolAtom("ab"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected =
      ClkAcceptOn(BoolAtom("ab"), ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, SyncAcceptOnConjoinsClockAndBecomesAcceptOn) {
  auto input =
      ClkSyncAcceptOn(BoolAtom("ab"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkAcceptOn(BoolAnd(BoolAtom("ab"), BoolAtom("clk")),
                              ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, NegationClocksItsBody) {
  auto input = ClkNot(ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkNot(ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, ImplicationClocksAntecedentAndConsequent) {
  auto input = ClkImplication(SeqBoolean(BoolAtom("a")),
                              ClkStrong(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkImplication(ClockedBoolean("clk", "a"),
                                 ClkStrong(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, OrDistributesClock) {
  auto input = ClkOr(ClkStrong(SeqBoolean(BoolAtom("a"))),
                     ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkOr(ClkStrong(ClockedBoolean("clk", "a")),
                        ClkWeak(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, AndDistributesClock) {
  auto input = ClkAnd(ClkStrong(SeqBoolean(BoolAtom("a"))),
                      ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkAnd(ClkStrong(ClockedBoolean("clk", "a")),
                         ClkWeak(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, NexttimeExpandsToClockGatedUntil) {
  auto body = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto input = ClkNexttime(body);
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));

  auto inner = ClkStrong(ClockedBoolean("clk", "a"));
  auto not_clock = ClkBoolean(BoolNot(BoolAtom("clk")));
  auto on_clock = ClkBoolean(BoolAtom("clk"));
  auto wait_then_body = ClkUntil(not_clock, ClkAnd(on_clock, inner));
  auto step = ClkNexttime(wait_then_body);
  auto expected = ClkUntil(not_clock, ClkAnd(on_clock, step));

  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, UntilGatesBothOperandsOnTheClock) {
  auto input = ClkUntil(ClkStrong(SeqBoolean(BoolAtom("a"))),
                        ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));

  auto left = ClkStrong(ClockedBoolean("clk", "a"));
  auto right = ClkWeak(ClockedBoolean("clk", "b"));
  auto on_clock = ClkBoolean(BoolAtom("clk"));
  auto guard = ClkNot(ClkAnd(on_clock, ClkNot(left)));
  auto release = ClkAnd(on_clock, right);
  auto expected = ClkUntil(guard, release);

  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, BooleanPropertyIsUnchanged) {
  auto input = ClkBoolean(BoolAtom("a"));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *ClkBoolean(BoolAtom("a"))));
}

TEST(PropertyClockRewrite, NestedClocksSupersedeRecursively) {
  auto input =
      ClkClock(BoolAtom("c2"),
               ClkClock(BoolAtom("c3"), ClkStrong(SeqBoolean(BoolAtom("a")))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("c1"));
  auto expected = ClkStrong(ClockedBoolean("c3", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite,
     IncomingClockReachesBareOperandWhileNestedClockOverrides) {
  auto clocked_left =
      ClkClock(BoolAtom("c2"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto bare_right = ClkWeak(SeqBoolean(BoolAtom("b")));
  auto input = ClkOr(clocked_left, bare_right);
  auto result = RewritePropertyUnderClock(*input, BoolAtom("c1"));
  auto expected = ClkOr(ClkStrong(ClockedBoolean("c2", "a")),
                        ClkWeak(ClockedBoolean("c1", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, NexttimeRecursesIntoCompoundBody) {
  auto body = ClkNot(ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto input = ClkNexttime(body);
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));

  auto inner = ClkNot(ClkStrong(ClockedBoolean("clk", "a")));
  auto not_clock = ClkBoolean(BoolNot(BoolAtom("clk")));
  auto on_clock = ClkBoolean(BoolAtom("clk"));
  auto wait_then_body = ClkUntil(not_clock, ClkAnd(on_clock, inner));
  auto step = ClkNexttime(wait_then_body);
  auto expected = ClkUntil(not_clock, ClkAnd(on_clock, step));

  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

TEST(PropertyClockRewrite, TheResultIsAnUnclockedProperty) {
  auto clocked_seq = SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("a")));
  auto under_nexttime =
      ClkNexttime(ClkClock(BoolAtom("c3"), ClkStrong(clocked_seq)));
  auto under_implication = ClkImplication(clocked_seq, ClkWeak(clocked_seq));
  auto under_until = ClkUntil(
      ClkSyncAcceptOn(BoolAtom("ab"), ClkStrong(SeqBoolean(BoolAtom("b")))),
      ClkNot(ClkDisableIff(BoolAtom("rst"), ClkStrong(clocked_seq))));
  for (const auto& input : {under_nexttime, under_implication, under_until,
                            ClkOr(under_nexttime, under_until),
                            ClkAnd(under_implication, under_nexttime)}) {
    EXPECT_FALSE(PropertyIsUnclocked(*input));
    EXPECT_TRUE(PropertyIsUnclocked(
        *RewritePropertyUnderClock(*input, BoolAtom("c1"))));
  }
}

TEST(PropertyClockRewrite, AnUnclockedPropertyHasNoClockAtAnyDepth) {
  auto bare = ClkStrong(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(PropertyIsUnclocked(*ClkBoolean(BoolAtom("a"))));
  EXPECT_TRUE(PropertyIsUnclocked(*ClkAcceptOn(BoolAtom("ab"), bare)));
  EXPECT_TRUE(PropertyIsUnclocked(*ClkUntil(bare, ClkNot(bare))));
  EXPECT_FALSE(PropertyIsUnclocked(*ClkClock(BoolAtom("c"), bare)));
  EXPECT_FALSE(PropertyIsUnclocked(*ClkSyncAcceptOn(BoolAtom("ab"), bare)));
  auto clocked_seq = SeqClock(BoolAtom("c"), SeqBoolean(BoolAtom("a")));
  EXPECT_FALSE(PropertyIsUnclocked(
      *ClkAnd(bare, ClkNot(ClkOr(bare, ClkWeak(clocked_seq))))));
  EXPECT_FALSE(PropertyIsUnclocked(
      *ClkAnd(bare, ClkNot(ClkOr(bare, ClkClock(BoolAtom("c"), bare))))));
  EXPECT_FALSE(PropertyIsUnclocked(*ClkImplication(clocked_seq, ClkNot(bare))));
}

}  // namespace
