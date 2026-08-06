#include <gtest/gtest.h>

#include "elaborator/semantic_leading_clock.h"
#include "elaborator/sequence_admits_empty.h"

using namespace delta;

namespace {

TEST(SemanticLeadingClock, BareSequenceIsInherited) {
  // §16.16.1: the semantic leading clock of a bare sequence s is inherited.
  auto c = SequenceLeadingClockOfBareSequence();
  EXPECT_TRUE(c.inherited);
}

TEST(SemanticLeadingClock, AtCReplacesInherited) {
  // §16.16.1: if inherited is the semantic leading clock of m, then the
  // semantic leading clock of @(c) m is c.
  auto inner = InheritedLeadingClock();
  auto outer = SequenceLeadingClockAfterAtC("posedge clk", inner);
  EXPECT_FALSE(outer.inherited);
  EXPECT_EQ(outer.event_expression, "posedge clk");
}

TEST(SemanticLeadingClock, AtCKeepsExplicitInnerClock) {
  // §16.16.1: otherwise the semantic leading clock of @(c) m equals the
  // semantic leading clock of m.
  auto inner = ExplicitLeadingClock("posedge a");
  auto outer = SequenceLeadingClockAfterAtC("posedge b", inner);
  EXPECT_FALSE(outer.inherited);
  EXPECT_EQ(outer.event_expression, "posedge a");
}

TEST(SemanticLeadingClock, ParenthesizedKeepsInnerClock) {
  // §16.16.1: the semantic leading clock of (m) equals the semantic leading
  // clock of m, whether that clock is inherited or explicit.
  auto explicit_inner = ExplicitLeadingClock("posedge clk");
  auto paren_explicit = SequenceLeadingClockOfParenthesized(explicit_inner);
  EXPECT_FALSE(paren_explicit.inherited);
  EXPECT_EQ(paren_explicit.event_expression, "posedge clk");

  auto inherited_inner = InheritedLeadingClock();
  auto paren_inherited = SequenceLeadingClockOfParenthesized(inherited_inner);
  EXPECT_TRUE(paren_inherited.inherited);
}

TEST(SemanticLeadingClock, DelayKeepsLeftClock) {
  // §16.16.1: m1 ##1 m2 and m1 ##0 m2 keep m1's leading clock.
  auto left = ExplicitLeadingClock("posedge clk0");
  auto right = ExplicitLeadingClock("posedge clk1");
  auto out = SequenceLeadingClockOfDelay(left, right);
  EXPECT_EQ(out.event_expression, "posedge clk0");
}

TEST(LeadingClockSet, StrongOfSeqGivesSequenceUniqueClock) {
  // §16.16.1: strong(m) has the singleton set {c} where c is m's unique
  // semantic leading clock.
  auto seq = ExplicitLeadingClock("posedge clk");
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kStrongOfMulticlockedSeq,
                             {}, {}, "", seq);
  EXPECT_TRUE(HasUniqueSemanticLeadingClock(s));
  EXPECT_EQ(*s.begin(), "posedge clk");
}

TEST(LeadingClockSet, AndUnionsChildren) {
  // §16.16.1: the set of semantic leading clocks of q1 and q2 is the union
  // of the two children's sets.
  LeadingClockSet a{std::string{"posedge clk1"}};
  LeadingClockSet b{std::string{"posedge clk2"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kAnd, a, b, "",
                             InheritedLeadingClock());
  EXPECT_EQ(s.size(), 2u);
}

TEST(LeadingClockSet, ImplicationUsesAntecedentSet) {
  // §16.16.1: m |-> p and m |=> p inherit m's set, not p's.
  LeadingClockSet ante{std::string{"posedge clkA"}};
  LeadingClockSet cons{std::string{"posedge clkC"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kOverlappingImplication,
                             ante, cons, "", InheritedLeadingClock());
  EXPECT_EQ(s.size(), 1u);
  EXPECT_EQ(*s.begin(), "posedge clkA");
}

TEST(LeadingClockSet, AtCReplacesInheritedInOperandSet) {
  // §16.16.1: @(c) q is obtained from q's set by replacing inherited with c.
  LeadingClockSet a{std::string{InheritedSentinel()}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kClockedAtProperty, a,
                             {}, "posedge clk", InheritedLeadingClock());
  EXPECT_TRUE(HasUniqueSemanticLeadingClock(s));
  EXPECT_EQ(*s.begin(), "posedge clk");
}

TEST(LeadingClockSet, AtCLeavesFullyClockedSetUnchanged) {
  // §16.16.1: @(c) q replaces inherited with c only when inherited is present
  // in q's set. Otherwise — when every element is already a real clock — the
  // set is left unchanged and the enclosing clock c is not introduced.
  LeadingClockSet already_clocked{std::string{"posedge clkA"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kClockedAtProperty,
                             already_clocked, {}, "posedge clkB",
                             InheritedLeadingClock());
  EXPECT_EQ(s, already_clocked);
}

TEST(LeadingClockSet, StrongAndWeakOfInheritedSeqGiveInheritedSet) {
  // §16.16.1: strong(m) and weak(m) take the singleton {c} where c is m's
  // unique semantic leading clock. When that clock is itself inherited — as a
  // bare multiclocked sequence is — the resulting set is the inherited
  // singleton, which is not yet a usable unique clock.
  auto inherited_seq = InheritedLeadingClock();
  auto strong =
      LeadingClockSetOf(PropertyLeadingClockForm::kStrongOfMulticlockedSeq, {},
                        {}, "", inherited_seq);
  auto weak =
      LeadingClockSetOf(PropertyLeadingClockForm::kWeakOfMulticlockedSeq, {},
                        {}, "", inherited_seq);
  ASSERT_EQ(strong.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*strong.begin()));
  EXPECT_FALSE(HasUniqueSemanticLeadingClock(strong));
  ASSERT_EQ(weak.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*weak.begin()));
  EXPECT_FALSE(HasUniqueSemanticLeadingClock(weak));
}

TEST(LeadingClockSet, UniqueClockRejectsInheritedSingleton) {
  // §16.16.1: a maximal multiclocked property must have a unique semantic
  // leading clock. An inherited singleton is not a usable unique clock —
  // there is no outer scope to fill it.
  LeadingClockSet only_inherited{std::string{InheritedSentinel()}};
  EXPECT_FALSE(HasUniqueSemanticLeadingClock(only_inherited));
}

TEST(LeadingClockSet, TwoDistinctClocksAreNotUnique) {
  // §16.16.1 (final paragraph, the wire clk1/clk2 example): a multiclocked
  // property has a unique semantic leading clock only when all of its leading
  // clocks are identical. Two distinct clocking events — as produced by
  // `@(clk1) a and @(clk2) b` — union into a two-element set, which is not a
  // unique semantic leading clock even though both events might sample equal
  // values. Build the set through this subclause's own `and` rule rather than
  // hand-assembling it.
  LeadingClockSet clk1{std::string{"posedge clk1"}};
  LeadingClockSet clk2{std::string{"posedge clk2"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kAnd, clk1, clk2, "",
                             InheritedLeadingClock());
  ASSERT_EQ(s.size(), 2u);
  EXPECT_FALSE(HasUniqueSemanticLeadingClock(s));
}

TEST(LeadingClockSet, WeakOfSeqGivesSequenceUniqueClock) {
  // §16.16.1: weak(m) has the singleton {c} where c is m's unique semantic
  // leading clock — same shape as strong(m).
  auto seq = ExplicitLeadingClock("posedge clk");
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kWeakOfMulticlockedSeq,
                             {}, {}, "", seq);
  EXPECT_TRUE(HasUniqueSemanticLeadingClock(s));
  EXPECT_EQ(*s.begin(), "posedge clk");
}

TEST(LeadingClockSet, BarePropertyHasInheritedSingleton) {
  // §16.16.1: a property p (with no enclosing clock) has the inherited
  // singleton set.
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kBareProperty, {}, {},
                             "", InheritedLeadingClock());
  ASSERT_EQ(s.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*s.begin()));
}

TEST(LeadingClockSet, ParenthesizedKeepsInnerSet) {
  // §16.16.1: (q) has the leading clock set of q.
  LeadingClockSet inner{std::string{"posedge clkP"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kParenthesized, inner,
                             {}, "", InheritedLeadingClock());
  EXPECT_EQ(s, inner);
}

TEST(LeadingClockSet, NotKeepsInnerSet) {
  // §16.16.1: not q has the leading clock set of q.
  LeadingClockSet inner{std::string{"posedge clkN"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kNot, inner, {}, "",
                             InheritedLeadingClock());
  EXPECT_EQ(s, inner);
}

TEST(LeadingClockSet, OrUnionsChildren) {
  // §16.16.1: q1 or q2 unions the children's sets, same as and.
  LeadingClockSet a{std::string{"posedge clk1"}};
  LeadingClockSet b{std::string{"posedge clk2"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kOr, a, b, "",
                             InheritedLeadingClock());
  EXPECT_EQ(s.size(), 2u);
}

TEST(LeadingClockSet, NonoverlappingImplicationUsesAntecedentSet) {
  // §16.16.1: m |=> p uses m's leading clock set, not p's.
  LeadingClockSet ante{std::string{"posedge clkAnte"}};
  LeadingClockSet cons{std::string{"posedge clkCons"}};
  auto s =
      LeadingClockSetOf(PropertyLeadingClockForm::kNonoverlappingImplication,
                        ante, cons, "", InheritedLeadingClock());
  ASSERT_EQ(s.size(), 1u);
  EXPECT_EQ(*s.begin(), "posedge clkAnte");
}

TEST(LeadingClockSet, IfThenAndIfElseHaveInheritedSet) {
  // §16.16.1: if (b) q and if (b) q1 else q2 both have the inherited
  // singleton set, regardless of the children's clocks.
  LeadingClockSet inner{std::string{"posedge clkIn"}};
  auto if_then = LeadingClockSetOf(PropertyLeadingClockForm::kIfThen, inner, {},
                                   "", InheritedLeadingClock());
  auto if_else = LeadingClockSetOf(PropertyLeadingClockForm::kIfElse, inner,
                                   inner, "", InheritedLeadingClock());
  ASSERT_EQ(if_then.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*if_then.begin()));
  ASSERT_EQ(if_else.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*if_else.begin()));
}

TEST(LeadingClockSet, CaseHasInheritedSet) {
  // §16.16.1: case ... endcase has the inherited singleton set.
  LeadingClockSet branch{std::string{"posedge clkB"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kCase, branch, {}, "",
                             InheritedLeadingClock());
  ASSERT_EQ(s.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*s.begin()));
}

TEST(LeadingClockSet, TemporalOperatorsHaveInheritedSet) {
  // §16.16.1: nexttime, always, s_eventually, until, and until_with all
  // have the inherited singleton set.
  LeadingClockSet inner{std::string{"posedge clk"}};
  for (auto form :
       {PropertyLeadingClockForm::kNexttime, PropertyLeadingClockForm::kAlways,
        PropertyLeadingClockForm::kSEventually,
        PropertyLeadingClockForm::kUntil,
        PropertyLeadingClockForm::kUntilWith}) {
    auto s = LeadingClockSetOf(form, inner, inner, "", InheritedLeadingClock());
    ASSERT_EQ(s.size(), 1u) << "form index " << static_cast<int>(form);
    EXPECT_TRUE(IsInheritedSentinel(*s.begin()))
        << "form index " << static_cast<int>(form);
  }
}

TEST(LeadingClockSet, AcceptOnAndRejectOnKeepOperandSet) {
  // §16.16.1: accept_on (b) q and reject_on (b) q keep q's leading clock
  // set unchanged.
  LeadingClockSet inner{std::string{"posedge clkX"}};
  auto accept = LeadingClockSetOf(PropertyLeadingClockForm::kAcceptOn, inner,
                                  {}, "", InheritedLeadingClock());
  auto reject = LeadingClockSetOf(PropertyLeadingClockForm::kRejectOn, inner,
                                  {}, "", InheritedLeadingClock());
  EXPECT_EQ(accept, inner);
  EXPECT_EQ(reject, inner);
}

TEST(LeadingClockSet, SyncAcceptOnAndSyncRejectOnHaveInheritedSet) {
  // §16.16.1: sync_accept_on (b) q and sync_reject_on (b) q have the
  // inherited singleton set.
  LeadingClockSet inner{std::string{"posedge clkY"}};
  auto sa = LeadingClockSetOf(PropertyLeadingClockForm::kSyncAcceptOn, inner,
                              {}, "", InheritedLeadingClock());
  auto sr = LeadingClockSetOf(PropertyLeadingClockForm::kSyncRejectOn, inner,
                              {}, "", InheritedLeadingClock());
  ASSERT_EQ(sa.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*sa.begin()));
  ASSERT_EQ(sr.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*sr.begin()));
}

TEST(LeadingClockSet, PropertyInstanceMirrorsFlattenedBody) {
  // §16.16.1: a property instance's leading-clock set equals the set of the
  // flattened body it stands for, after actual-argument substitution.
  LeadingClockSet body{std::string{"posedge clkBody"}};
  auto s = LeadingClockSetOfPropertyInstance(body);
  EXPECT_EQ(s, body);
}

}  // namespace
