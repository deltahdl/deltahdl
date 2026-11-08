#include <gtest/gtest.h>

#include "elaborator/semantic_leading_clock.h"
#include "elaborator/sequence_admits_empty.h"

using namespace delta;

namespace {

TEST(SemanticLeadingClock, BareSequenceIsInherited) {
  auto c = SequenceLeadingClockOfBareSequence();
  EXPECT_TRUE(c.inherited);
}

TEST(SemanticLeadingClock, AtCReplacesInherited) {
  auto inner = InheritedLeadingClock();
  auto outer = SequenceLeadingClockAfterAtC("posedge clk", inner);
  EXPECT_FALSE(outer.inherited);
  EXPECT_EQ(outer.event_expression, "posedge clk");
}

TEST(SemanticLeadingClock, AtCKeepsExplicitInnerClock) {
  auto inner = ExplicitLeadingClock("posedge a");
  auto outer = SequenceLeadingClockAfterAtC("posedge b", inner);
  EXPECT_FALSE(outer.inherited);
  EXPECT_EQ(outer.event_expression, "posedge a");
}

TEST(SemanticLeadingClock, ParenthesizedKeepsInnerClock) {
  auto explicit_inner = ExplicitLeadingClock("posedge clk");
  auto paren_explicit = SequenceLeadingClockOfParenthesized(explicit_inner);
  EXPECT_FALSE(paren_explicit.inherited);
  EXPECT_EQ(paren_explicit.event_expression, "posedge clk");

  auto inherited_inner = InheritedLeadingClock();
  auto paren_inherited = SequenceLeadingClockOfParenthesized(inherited_inner);
  EXPECT_TRUE(paren_inherited.inherited);
}

TEST(SemanticLeadingClock, DelayKeepsLeftClock) {
  auto left = ExplicitLeadingClock("posedge clk0");
  auto right = ExplicitLeadingClock("posedge clk1");
  auto out = SequenceLeadingClockOfDelay(left, right);
  EXPECT_EQ(out.event_expression, "posedge clk0");
}

TEST(LeadingClockSet, StrongOfSeqGivesSequenceUniqueClock) {
  auto seq = ExplicitLeadingClock("posedge clk");
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kStrongOfMulticlockedSeq,
                             {}, {}, "", seq);
  EXPECT_TRUE(HasUniqueSemanticLeadingClock(s));
  EXPECT_EQ(*s.begin(), "posedge clk");
}

TEST(LeadingClockSet, AndUnionsChildren) {
  LeadingClockSet a{std::string{"posedge clk1"}};
  LeadingClockSet b{std::string{"posedge clk2"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kAnd, a, b, "",
                             InheritedLeadingClock());
  EXPECT_EQ(s.size(), 2u);
}

TEST(LeadingClockSet, ImplicationUsesAntecedentSet) {
  LeadingClockSet ante{std::string{"posedge clkA"}};
  LeadingClockSet cons{std::string{"posedge clkC"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kOverlappingImplication,
                             ante, cons, "", InheritedLeadingClock());
  EXPECT_EQ(s.size(), 1u);
  EXPECT_EQ(*s.begin(), "posedge clkA");
}

TEST(LeadingClockSet, AtCReplacesInheritedInOperandSet) {
  LeadingClockSet a{std::string{InheritedSentinel()}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kClockedAtProperty, a,
                             {}, "posedge clk", InheritedLeadingClock());
  EXPECT_TRUE(HasUniqueSemanticLeadingClock(s));
  EXPECT_EQ(*s.begin(), "posedge clk");
}

TEST(LeadingClockSet, AtCLeavesFullyClockedSetUnchanged) {
  LeadingClockSet already_clocked{std::string{"posedge clkA"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kClockedAtProperty,
                             already_clocked, {}, "posedge clkB",
                             InheritedLeadingClock());
  EXPECT_EQ(s, already_clocked);
}

TEST(LeadingClockSet, StrongAndWeakOfInheritedSeqGiveInheritedSet) {
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
  LeadingClockSet only_inherited{std::string{InheritedSentinel()}};
  EXPECT_FALSE(HasUniqueSemanticLeadingClock(only_inherited));
}

TEST(LeadingClockSet, TwoDistinctClocksAreNotUnique) {
  LeadingClockSet clk1{std::string{"posedge clk1"}};
  LeadingClockSet clk2{std::string{"posedge clk2"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kAnd, clk1, clk2, "",
                             InheritedLeadingClock());
  ASSERT_EQ(s.size(), 2u);
  EXPECT_FALSE(HasUniqueSemanticLeadingClock(s));
}

TEST(LeadingClockSet, WeakOfSeqGivesSequenceUniqueClock) {
  auto seq = ExplicitLeadingClock("posedge clk");
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kWeakOfMulticlockedSeq,
                             {}, {}, "", seq);
  EXPECT_TRUE(HasUniqueSemanticLeadingClock(s));
  EXPECT_EQ(*s.begin(), "posedge clk");
}

TEST(LeadingClockSet, BarePropertyHasInheritedSingleton) {
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kBareProperty, {}, {},
                             "", InheritedLeadingClock());
  ASSERT_EQ(s.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*s.begin()));
}

TEST(LeadingClockSet, ParenthesizedKeepsInnerSet) {
  LeadingClockSet inner{std::string{"posedge clkP"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kParenthesized, inner,
                             {}, "", InheritedLeadingClock());
  EXPECT_EQ(s, inner);
}

TEST(LeadingClockSet, NotKeepsInnerSet) {
  LeadingClockSet inner{std::string{"posedge clkN"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kNot, inner, {}, "",
                             InheritedLeadingClock());
  EXPECT_EQ(s, inner);
}

TEST(LeadingClockSet, OrUnionsChildren) {
  LeadingClockSet a{std::string{"posedge clk1"}};
  LeadingClockSet b{std::string{"posedge clk2"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kOr, a, b, "",
                             InheritedLeadingClock());
  EXPECT_EQ(s.size(), 2u);
}

TEST(LeadingClockSet, NonoverlappingImplicationUsesAntecedentSet) {
  LeadingClockSet ante{std::string{"posedge clkAnte"}};
  LeadingClockSet cons{std::string{"posedge clkCons"}};
  auto s =
      LeadingClockSetOf(PropertyLeadingClockForm::kNonoverlappingImplication,
                        ante, cons, "", InheritedLeadingClock());
  ASSERT_EQ(s.size(), 1u);
  EXPECT_EQ(*s.begin(), "posedge clkAnte");
}

TEST(LeadingClockSet, IfThenAndIfElseHaveInheritedSet) {
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
  LeadingClockSet branch{std::string{"posedge clkB"}};
  auto s = LeadingClockSetOf(PropertyLeadingClockForm::kCase, branch, {}, "",
                             InheritedLeadingClock());
  ASSERT_EQ(s.size(), 1u);
  EXPECT_TRUE(IsInheritedSentinel(*s.begin()));
}

TEST(LeadingClockSet, TemporalOperatorsHaveInheritedSet) {
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
  LeadingClockSet inner{std::string{"posedge clkX"}};
  auto accept = LeadingClockSetOf(PropertyLeadingClockForm::kAcceptOn, inner,
                                  {}, "", InheritedLeadingClock());
  auto reject = LeadingClockSetOf(PropertyLeadingClockForm::kRejectOn, inner,
                                  {}, "", InheritedLeadingClock());
  EXPECT_EQ(accept, inner);
  EXPECT_EQ(reject, inner);
}

TEST(LeadingClockSet, SyncAcceptOnAndSyncRejectOnHaveInheritedSet) {
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
  LeadingClockSet body{std::string{"posedge clkBody"}};
  auto s = LeadingClockSetOfPropertyInstance(body);
  EXPECT_EQ(s, body);
}

}  // namespace
