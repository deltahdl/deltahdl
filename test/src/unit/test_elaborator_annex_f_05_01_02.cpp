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
TEST(PropertyRewrite, StrongDelegatesToSequenceRewrite) {
  auto input = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkStrong(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p(weak(r), c) = (weak(T^s(r, c))).
TEST(PropertyRewrite, WeakDelegatesToSequenceRewrite) {
  auto input = ClkWeak(SeqBoolean(BoolAtom("a")));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkWeak(ClockedBoolean("clk", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((@(c2) p), c1) = T^p(p, c2). The inner clock supersedes the
// incoming clock.
TEST(PropertyRewrite, NestedClockSupersedesIncomingClock) {
  auto input = ClkClock(BoolAtom("c2"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("c1"));
  auto expected = ClkStrong(ClockedBoolean("c2", "a"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((disable iff(b) p), c) = (disable iff(b) T^p(p, c)). The
// disable condition is preserved and the clock pushes into the body.
TEST(PropertyRewrite, DisableIffPreservesConditionAndClocksBody) {
  auto input =
      ClkDisableIff(BoolAtom("rst"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected =
      ClkDisableIff(BoolAtom("rst"), ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((accept_on(b) p), c) = (accept_on(b) T^p(p, c)). The
// asynchronous abort condition is left unchanged.
TEST(PropertyRewrite, AcceptOnLeavesConditionUntouched) {
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
TEST(PropertyRewrite, SyncAcceptOnConjoinsClockAndBecomesAcceptOn) {
  auto input =
      ClkSyncAcceptOn(BoolAtom("ab"), ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkAcceptOn(BoolAnd(BoolAtom("ab"), BoolAtom("clk")),
                              ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((not p), c) = (not T^p(p, c)).
TEST(PropertyRewrite, NegationClocksItsBody) {
  auto input = ClkNot(ClkStrong(SeqBoolean(BoolAtom("a"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkNot(ClkStrong(ClockedBoolean("clk", "a")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((r |-> p), c) = (T^s(r, c) |-> T^p(p, c)). The antecedent goes
// through the sequence rewrite, the consequent through the property rewrite.
TEST(PropertyRewrite, ImplicationClocksAntecedentAndConsequent) {
  auto input = ClkImplication(SeqBoolean(BoolAtom("a")),
                              ClkStrong(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkImplication(ClockedBoolean("clk", "a"),
                                 ClkStrong(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((p1 or p2), c) = (T^p(p1, c) or T^p(p2, c)).
TEST(PropertyRewrite, OrDistributesClock) {
  auto input = ClkOr(ClkStrong(SeqBoolean(BoolAtom("a"))),
                     ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkOr(ClkStrong(ClockedBoolean("clk", "a")),
                        ClkWeak(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((p1 and p2), c) = (T^p(p1, c) and T^p(p2, c)).
TEST(PropertyRewrite, AndDistributesClock) {
  auto input = ClkAnd(ClkStrong(SeqBoolean(BoolAtom("a"))),
                      ClkWeak(SeqBoolean(BoolAtom("b"))));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  auto expected = ClkAnd(ClkStrong(ClockedBoolean("clk", "a")),
                         ClkWeak(ClockedBoolean("clk", "b")));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *expected));
}

// §F.5.1.2: T^p((nexttime p), c) =
//   (!c until (c and nexttime(!c until (c and T^p(p, c))))).
TEST(PropertyRewrite, NexttimeExpandsToClockGatedUntil) {
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
TEST(PropertyRewrite, UntilGatesBothOperandsOnTheClock) {
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
TEST(PropertyRewrite, BooleanPropertyIsUnchanged) {
  auto input = ClkBoolean(BoolAtom("a"));
  auto result = RewritePropertyUnderClock(*input, BoolAtom("clk"));
  EXPECT_TRUE(ClockedPropertyEqual(*result, *ClkBoolean(BoolAtom("a"))));
}

// Edge case for §F.5.1.2: T^p((@(c2) p), c1) = T^p(p, c2). When two clock forms
// nest, the rule fires at each level, so the innermost clock wins and both
// outer clocks are discarded. This exercises the recursion the single-level
// test does not reach.
TEST(PropertyRewrite, NestedClocksSupersedeRecursively) {
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
TEST(PropertyRewrite,
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
TEST(PropertyRewrite, NexttimeRecursesIntoCompoundBody) {
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

}  // namespace
