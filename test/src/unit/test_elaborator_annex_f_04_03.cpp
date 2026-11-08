#include <gtest/gtest.h>

#include "elaborator/sequence_admits_empty.h"

using namespace delta;

namespace {

TEST(AdmitsEmpty, BooleanNeverAdmitsEmpty) {
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kBoolean, false, false));
}

TEST(AdmitsEmpty, LocalVarDeclPassesThroughToRest) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kLocalVarDeclThenRest, true, false));
  EXPECT_FALSE(
      AdmitsEmpty(AdmitsEmptyForm::kLocalVarDeclThenRest, false, false));
}

TEST(AdmitsEmpty, OneTickWithLocalVarAssignmentDoesNotAdmitEmpty) {
  EXPECT_FALSE(
      AdmitsEmpty(AdmitsEmptyForm::kOneTickWithLocalVarAssignment, true, true));
}

TEST(AdmitsEmpty, Delay1RequiresBothChildrenAdmitEmpty) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kDelay1, true, true));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kDelay1, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kDelay1, false, true));
}

TEST(AdmitsEmpty, Delay0NeverAdmitsEmpty) {
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kDelay0, true, true));
}

TEST(AdmitsEmpty, OrIsDisjunctiveOverChildren) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kOr, false, true));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kOr, false, false));
}

TEST(AdmitsEmpty, OrIsTrueWhenLeftChildAdmitsEmpty) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kOr, true, false));
}

TEST(AdmitsEmpty, IntersectIsConjunctiveOverChildren) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kIntersect, true, true));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kIntersect, true, false));
}

TEST(AdmitsEmpty, IntersectIsFalseWhenLeftChildDoesNotAdmitEmpty) {
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kIntersect, false, true));
}

TEST(AdmitsEmpty, FirstMatchPassesThroughInner) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kFirstMatch, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kFirstMatch, false, false));
}

TEST(AdmitsEmpty, StarZeroAlwaysAdmitsEmpty) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kStarZero, false, false));
}

TEST(AdmitsEmpty, PlusBoundedTracksInner) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kPlusBounded, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kPlusBounded, false, false));
}

TEST(AdmitsEmpty, ClockedAtPassesThroughInner) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kClockedAt, true, false));
}

TEST(AdmitsEmpty, ClockedAtIsFalseWhenInnerDoesNotAdmitEmpty) {
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kClockedAt, false, false));
}

TEST(KappaForLocalVarRewrite, InheritedYieldsEmptyString) {
  EXPECT_EQ(KappaForLocalVarRewrite(InheritedLeadingClock()), "");
}

TEST(KappaForLocalVarRewrite, ExplicitYieldsAtCSplice) {
  EXPECT_EQ(KappaForLocalVarRewrite(ExplicitLeadingClock("posedge clk")),
            "@(posedge clk)");
}

TEST(Push, LocalVarDeclSiteAlwaysPrepends) {
  EXPECT_EQ(RoutePush(PushSite::kLocalVarDeclThenProp, false, false),
            PushRouting::kPrependLocalVarDecl);
}

TEST(Push, SequenceAsPropertyCollapsesWhenListEmpty) {
  EXPECT_EQ(RoutePush(PushSite::kSequenceAsProperty, true, false),
            PushRouting::kRecurseInner);
}

TEST(Push, SequenceAsPropertySplicesKappaWithDelayZero) {
  EXPECT_EQ(RoutePush(PushSite::kSequenceAsProperty, false, false),
            PushRouting::kAttachKappaWithDelayZero);
}

TEST(Push, NonoverlappingImplicationSplitsOnEmptyAdmittingAntecedent) {
  EXPECT_EQ(RoutePush(PushSite::kNonoverlappingImplication, false, true),
            PushRouting::kRecurseBothBranches);
  EXPECT_EQ(RoutePush(PushSite::kNonoverlappingImplication, false, false),
            PushRouting::kAttachKappaWithDelayZero);
}

TEST(Push, OrAndRecurseIntoBothBranches) {
  EXPECT_EQ(RoutePush(PushSite::kOr, false, false),
            PushRouting::kRecurseBothBranches);
  EXPECT_EQ(RoutePush(PushSite::kAnd, false, false),
            PushRouting::kRecurseBothBranches);
}

TEST(Push, IfElseWithEmptyListRecursesIntoBothBranches) {
  EXPECT_EQ(RoutePush(PushSite::kIfElse, true, false),
            PushRouting::kRecurseBothBranches);
}

TEST(Push, IfElseWithNonEmptyListLiftsToImplicationGuard) {
  EXPECT_EQ(RoutePush(PushSite::kIfElse, false, false),
            PushRouting::kGuardWithImplicationThenBranches);
}

TEST(SequenceLocalVarDecl, NonEmptyRestDropsEmptyGuardArm) {
  EXPECT_EQ(RewriteSequenceLocalVarDecl(false),
            SequenceLocalVarDeclRewrite::kSimplifiedNonEmpty);
}

TEST(SequenceLocalVarDecl, EmptyAdmittingRestCollapsesGuardToStarZero) {
  EXPECT_EQ(RewriteSequenceLocalVarDecl(true),
            SequenceLocalVarDeclRewrite::kSimplifiedEmpty);
}

TEST(Push, DisableIffRecursesIntoInner) {
  EXPECT_EQ(RoutePush(PushSite::kDisableIff, false, false),
            PushRouting::kRecurseInner);
}

TEST(AdmitsEmpty, ParenthesizedTracksInner) {
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kParenthesized, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kParenthesized, false, false));
}

TEST(Push, LocalVarAssignmentPrependsThatAssignment) {
  EXPECT_EQ(RoutePush(PushSite::kLocalVarAssignThenProp, false, false),
            PushRouting::kPrependLocalVarAssignment);
}

TEST(Push, OverlappingImplicationCollapsesWhenListEmpty) {
  EXPECT_EQ(RoutePush(PushSite::kOverlappingImplication, true, false),
            PushRouting::kRecurseInner);
}

TEST(Push, OverlappingImplicationSplicesKappaWithDelayZeroWhenListNonEmpty) {
  EXPECT_EQ(RoutePush(PushSite::kOverlappingImplication, false, false),
            PushRouting::kAttachKappaWithDelayZero);
}

TEST(Push, NonoverlappingImplicationCollapsesWhenListEmpty) {
  EXPECT_EQ(RoutePush(PushSite::kNonoverlappingImplication, true, true),
            PushRouting::kRecurseInner);
}

TEST(Push, ClockedAtRecursesIntoInner) {
  EXPECT_EQ(RoutePush(PushSite::kClockedAtProp, false, false),
            PushRouting::kRecurseInner);
}

TEST(Push, ParenthesizedRecursesIntoInner) {
  EXPECT_EQ(RoutePush(PushSite::kParenthesized, false, false),
            PushRouting::kRecurseInner);
}

TEST(Push, NotRecursesIntoInner) {
  EXPECT_EQ(RoutePush(PushSite::kNot, false, false),
            PushRouting::kRecurseInner);
}

}  // namespace
