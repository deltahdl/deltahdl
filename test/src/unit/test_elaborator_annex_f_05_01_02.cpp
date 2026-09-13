#include <gtest/gtest.h>

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_sequence_rewrite.h"

using namespace delta;

namespace {

// The §F.5.1.1 result of clocking a single Boolean: (!c[*0:$] ##1 c & atom).
// T^p reuses T^s for sequence operands, so the strong/weak/implication
// expectations are stated in terms of it.
std::shared_ptr<const SequenceExpr> ClockedBoolean(const char* clock,
                                                   const char* atom) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(BoolAtom(clock)))),
                   SeqBoolean(BoolAnd(BoolAtom(clock), BoolAtom(atom))));
}

// §F.5.1.2: T^p(strong(r), c) = (strong(T^s(r, c))).
TEST(PropertyClockRewrite, StrongDelegatesToSequenceRewrite) {
  auto input = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkStrong(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p(weak(r), c) = (weak(T^s(r, c))).
TEST(PropertyClockRewrite, WeakDelegatesToSequenceRewrite) {
  auto input = ClkWeak(SeqBoolean(BoolAtom("a")));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkWeak(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((@(c2) p), c1) = T^p(p, c2). The inner clock supersedes the
// incoming clock.
TEST(PropertyClockRewrite, NestedClockSupersedesIncomingClock) {
  auto input = ClkClock(BoolAtom("c2"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("c1"));
  auto expected = ClkStrong(ClockedBoolean("c2", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((disable iff(b) p), c) = (disable iff(b) T^p(p, c)). The
// disable condition is preserved and the clock pushes into the body.
TEST(PropertyClockRewrite, DisableIffPreservesConditionAndClocksBody) {
  auto input =
      ClkDisableIff(BoolAtom("rst"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected =
      ClkDisableIff(BoolAtom("rst"), ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((accept_on(b) p), c) = (accept_on(b) T^p(p, c)). The
// asynchronous abort condition is left unchanged.
TEST(PropertyClockRewrite, AcceptOnLeavesConditionUntouched) {
  auto input =
      ClkAcceptOn(BoolAtom("ab"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected =
      ClkAcceptOn(BoolAtom("ab"), ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((sync_accept_on(b) p), c) = (accept_on(b && c) T^p(p, c)). The
// synchronous abort condition is conjoined with the clock and becomes a plain
// accept_on.
TEST(PropertyClockRewrite, SyncAcceptOnConjoinsClockAndBecomesAcceptOn) {
  auto input =
      ClkSyncAcceptOn(BoolAtom("ab"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkAcceptOn(BoolAnd(BoolAtom("ab"), BoolAtom("clk")),
                              ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((not p), c) = (not T^p(p, c)).
TEST(PropertyClockRewrite, NegationClocksItsBody) {
  auto input = ClkNot(ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkNot(ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((r |-> p), c) = (T^s(r, c) |-> T^p(p, c)). The antecedent goes
// through the sequence rewrite, the consequent through the property rewrite.
TEST(PropertyClockRewrite, ImplicationClocksAntecedentAndConsequent) {
  auto input = ClkImplication(SeqBoolean(BoolAtom("a")),
                              ClkStrong(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkImplication(ClockedBoolean("clk", "a"),
                                 ClkStrong(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((p1 or p2), c) = (T^p(p1, c) or T^p(p2, c)).
TEST(PropertyClockRewrite, OrDistributesClock) {
  auto input = ClkOr(ClkStrong(SeqBoolean(BoolAtom("a"))),
                     ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkOr(ClkStrong(ClockedBoolean("clk", "a")),
                        ClkWeak(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((p1 and p2), c) = (T^p(p1, c) and T^p(p2, c)).
TEST(PropertyClockRewrite, AndDistributesClock) {
  auto input = ClkAnd(ClkStrong(SeqBoolean(BoolAtom("a"))),
                      ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkAnd(ClkStrong(ClockedBoolean("clk", "a")),
                         ClkWeak(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((nexttime p), c) =
//   (!c until (c and nexttime(!c until (c and T^p(p, c))))).
TEST(PropertyClockRewrite, NexttimeExpandsToClockGatedUntil) {
  auto body = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto input = ClkNexttime(body);
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));

  auto inner = ClkStrong(ClockedBoolean("clk", "a"));  // T^p(p, c)
  auto not_clock = ClkBoolean(BoolNot(BoolAtom("clk")));
  auto on_clock = ClkBoolean(BoolAtom("clk"));
  auto wait_then_body = ClkUntil(not_clock, ClkAnd(on_clock, inner));
  auto step = ClkNexttime(wait_then_body);
  auto expected = ClkUntil(not_clock, ClkAnd(on_clock, step));

  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((p1 until p2), c) =
//   ((not(c and not T^p(p1, c))) until (c and T^p(p2, c))).
TEST(PropertyClockRewrite, UntilGatesBothOperandsOnTheClock) {
  auto input = ClkUntil(ClkStrong(SeqBoolean(BoolAtom("a"))),
                        ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));

  auto left = ClkStrong(ClockedBoolean("clk", "a"));  // T^p(p1, c)
  auto right = ClkWeak(ClockedBoolean("clk", "b"));   // T^p(p2, c)
  auto on_clock = ClkBoolean(BoolAtom("clk"));
  auto guard = ClkNot(ClkAnd(on_clock, ClkNot(left)));
  auto release = ClkAnd(on_clock, right);
  auto expected = ClkUntil(guard, release);

  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// A Boolean used as a property is already level-sensitive: T^p leaves it as is.
// This exercises the leaf the nexttime/until rules emit.
TEST(PropertyClockRewrite, BooleanPropertyIsUnchanged) {
  auto input = ClkBoolean(BoolAtom("a"));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *ClkBoolean(BoolAtom("a"))));
}

// Edge case for §F.5.1.2: T^p((@(c2) p), c1) = T^p(p, c2). When two clock forms
// nest, the rule fires at each level, so the innermost clock wins and both
// outer clocks are discarded. This exercises the recursion the single-level
// test does not reach.
TEST(PropertyClockRewrite, NestedClocksSupersedeRecursively) {
  auto input =
      ClkClock(BoolAtom("c2"),
               ClkClock(BoolAtom("c3"), ClkStrong(SeqBoolean(BoolAtom("a")))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("c1"));
  auto expected = ClkStrong(ClockedBoolean("c3", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// Edge case combining §F.5.1.2's or rule with the nested-clock rule: when one
// operand carries its own clock and the other does not, the incoming clock must
// recurse into the bare operand while the nested clock overrides locally. This
// confirms T^p descends through an operator before any inner clock takes over.
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

// Edge case for §F.5.1.2's nexttime rule: its body is itself a compound
// property, so T^p must recurse into it before wrapping the result in the
// clock-gated until/nexttime scaffold. Here the body is (not strong(a)).
TEST(PropertyClockRewrite, NexttimeRecursesIntoCompoundBody) {
  auto body = ClkNot(ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto input = ClkNexttime(body);
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));

  auto inner = ClkNot(ClkStrong(ClockedBoolean("clk", "a")));  // T^p(body, c)
  auto not_clock = ClkBoolean(BoolNot(BoolAtom("clk")));
  auto on_clock = ClkBoolean(BoolAtom("clk"));
  auto wait_then_body = ClkUntil(not_clock, ClkAnd(on_clock, inner));
  auto step = ClkNexttime(wait_then_body);
  auto expected = ClkUntil(not_clock, ClkAnd(on_clock, step));

  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2 produces a property P from a property p: whatever clocks the input
// carries, the rules leave none behind. A clock nested under every operator
// -- a clock form inside a nexttime body, a clocked sequence operand of a
// strong and of an implication, a sync_accept_on under an until -- is
// removed by the rule for its form, so the input is clocked at each of those
// depths and the result is not.
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

// The unclocked property is the one with no clock form, no sync_accept_on
// and no clocked sequence operand at any depth: a Boolean, an accept_on over
// a strong of a bare sequence and an until of two such are unclocked, where
// a clock form, a sync_accept_on or a clocked sequence operand nested three
// levels down makes the property clocked.
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
