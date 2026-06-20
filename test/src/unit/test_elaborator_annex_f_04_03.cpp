#include <gtest/gtest.h>

#include "elaborator/semantic_leading_clock.h"
#include "elaborator/sequence_admits_empty.h"

using namespace delta;

namespace {

TEST(AdmitsEmpty, BooleanNeverAdmitsEmpty) {
  // §F.4.3: admits_empty(b) = 0.
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kBoolean, false, false));
}

TEST(AdmitsEmpty, LocalVarDeclPassesThroughToRest) {
  // §F.4.3: admits_empty((t v [= e]; r)) = admits_empty(r).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kLocalVarDeclThenRest,
                          /*first=*/true, /*second=*/false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kLocalVarDeclThenRest,
                           /*first=*/false, /*second=*/false));
}

TEST(AdmitsEmpty, OneTickWithLocalVarAssignmentDoesNotAdmitEmpty) {
  // §F.4.3: admits_empty((1, v = e)) = 0.
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kOneTickWithLocalVarAssignment,
                           /*first=*/true, /*second=*/true));
}

TEST(AdmitsEmpty, Delay1RequiresBothChildrenAdmitEmpty) {
  // §F.4.3: admits_empty((r1 ##1 r2)) = admits_empty(r1) && admits_empty(r2).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kDelay1, true, true));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kDelay1, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kDelay1, false, true));
}

TEST(AdmitsEmpty, Delay0NeverAdmitsEmpty) {
  // §F.4.3: admits_empty((r1 ##0 r2)) = 0.
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kDelay0, true, true));
}

TEST(AdmitsEmpty, OrIsDisjunctiveOverChildren) {
  // §F.4.3: admits_empty((r1 or r2)) = admits_empty(r1) || admits_empty(r2).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kOr, false, true));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kOr, false, false));
}

TEST(AdmitsEmpty, IntersectIsConjunctiveOverChildren) {
  // §F.4.3: admits_empty((r1 intersect r2)) = admits_empty(r1) &&
  // admits_empty(r2).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kIntersect, true, true));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kIntersect, true, false));
}

TEST(AdmitsEmpty, FirstMatchPassesThroughInner) {
  // §F.4.3: admits_empty(first_match(r)) = admits_empty(r).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kFirstMatch, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kFirstMatch, false, false));
}

TEST(AdmitsEmpty, StarZeroAlwaysAdmitsEmpty) {
  // §F.4.3: admits_empty(r[*0]) = 1. This is also the §16.12.22 anchor for
  // sequences that admit only empty matches.
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kStarZero, false, false));
}

TEST(AdmitsEmpty, PlusBoundedTracksInner) {
  // §F.4.3: admits_empty(r[*1:$]) = admits_empty(r).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kPlusBounded, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kPlusBounded, false, false));
}

TEST(AdmitsEmpty, ClockedAtPassesThroughInner) {
  // §F.4.3: admits_empty(@(c) r) = admits_empty(r).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kClockedAt, true, false));
}

TEST(KappaForLocalVarRewrite, InheritedYieldsEmptyString) {
  // §F.4.3: when the leading clock is inherited, κ(r) is the empty string.
  // §16.16.1 owns the notion of an inherited leading clock; §F.4.3 reuses
  // it to gate whether a "@(c)" splice is needed.
  EXPECT_EQ(KappaForLocalVarRewrite(InheritedLeadingClock()), "");
}

TEST(KappaForLocalVarRewrite, ExplicitYieldsAtCSplice) {
  // §F.4.3: otherwise κ(r) is "@(c)" where c is the leading clock event.
  EXPECT_EQ(KappaForLocalVarRewrite(ExplicitLeadingClock("posedge clk")),
            "@(posedge clk)");
}

TEST(Push, LocalVarDeclSiteAlwaysPrepends) {
  // §F.4.3: push(E, (t v; p)) = (t v; push(E, p)).
  EXPECT_EQ(RoutePush(PushSite::kLocalVarDeclThenProp,
                      /*list_empty=*/false,
                      /*right_admits_empty=*/false),
            PushRouting::kPrependLocalVarDecl);
}

TEST(Push, SequenceAsPropertyCollapsesWhenListEmpty) {
  // §F.4.3: push(<>, r) = r when r is used as a property.
  EXPECT_EQ(RoutePush(PushSite::kSequenceAsProperty,
                      /*list_empty=*/true,
                      /*right_admits_empty=*/false),
            PushRouting::kRecurseInner);
}

TEST(Push, SequenceAsPropertySplicesKappaWithDelayZero) {
  // §F.4.3: push(E, r) = κ(r) (1, E) ##0 r otherwise — the κ helper splices
  // an @(c) prefix sourced from §16.16.1, then ##0 to anchor the
  // assignments at the start of the match.
  EXPECT_EQ(RoutePush(PushSite::kSequenceAsProperty,
                      /*list_empty=*/false,
                      /*right_admits_empty=*/false),
            PushRouting::kAttachKappaWithDelayZero);
}

TEST(Push, NonoverlappingImplicationSplitsOnEmptyAdmittingAntecedent) {
  // §F.4.3: when the antecedent admits an empty match, push(<>, r |=> p)
  // diverges into a two-branch rewrite — that is the cross-link to
  // §16.12.22's nondegeneracy classes.
  EXPECT_EQ(RoutePush(PushSite::kNonoverlappingImplication,
                      /*list_empty=*/false,
                      /*right_admits_empty=*/true),
            PushRouting::kRecurseBothBranches);
  EXPECT_EQ(RoutePush(PushSite::kNonoverlappingImplication,
                      /*list_empty=*/false,
                      /*right_admits_empty=*/false),
            PushRouting::kAttachKappaWithDelayZero);
}

TEST(Push, IfElseAndOrRecurseIntoBothBranches) {
  // §F.4.3: push for if/else, or, and and uniformly recurses into both
  // branches.
  EXPECT_EQ(RoutePush(PushSite::kIfElse, false, false),
            PushRouting::kRecurseBothBranches);
  EXPECT_EQ(RoutePush(PushSite::kOr, false, false),
            PushRouting::kRecurseBothBranches);
  EXPECT_EQ(RoutePush(PushSite::kAnd, false, false),
            PushRouting::kRecurseBothBranches);
}

TEST(Push, DisableIffRecursesIntoInner) {
  // §F.4.3: push(E, disable iff (b) p) = disable iff (b) push(E, p) — the
  // disable iff wrapper does not move the assignments past itself.
  EXPECT_EQ(RoutePush(PushSite::kDisableIff, false, false),
            PushRouting::kRecurseInner);
}

TEST(AdmitsEmpty, ParenthesizedTracksInner) {
  // §F.4.3: admits_empty((r)) = admits_empty(r).
  EXPECT_TRUE(AdmitsEmpty(AdmitsEmptyForm::kParenthesized, true, false));
  EXPECT_FALSE(AdmitsEmpty(AdmitsEmptyForm::kParenthesized, false, false));
}

TEST(Push, LocalVarAssignmentPrependsThatAssignment) {
  // §F.4.3: push(E, (t v = e; p)) = (t v; push(<E, v=e>, p)) — the
  // declaration's initializer becomes a new entry in the assignment list.
  EXPECT_EQ(RoutePush(PushSite::kLocalVarAssignThenProp,
                      /*list_empty=*/false,
                      /*right_admits_empty=*/false),
            PushRouting::kPrependLocalVarAssignment);
}

TEST(Push, OverlappingImplicationCollapsesWhenListEmpty) {
  // §F.4.3: push(<>, r |-> p) = r |-> push(<>, p) — when the assignment
  // list is empty, the antecedent stays put and only the consequent is
  // pushed into.
  EXPECT_EQ(RoutePush(PushSite::kOverlappingImplication,
                      /*list_empty=*/true,
                      /*right_admits_empty=*/false),
            PushRouting::kRecurseInner);
}

TEST(Push, NonoverlappingImplicationCollapsesWhenListEmpty) {
  // §F.4.3: push(<>, r |=> p) = r |=> push(<>, p). The empty-list branch
  // ignores the antecedent's empty-match classification.
  EXPECT_EQ(RoutePush(PushSite::kNonoverlappingImplication,
                      /*list_empty=*/true,
                      /*right_admits_empty=*/true),
            PushRouting::kRecurseInner);
}

TEST(Push, ClockedAtRecursesIntoInner) {
  // §F.4.3: push(E, @(c) p) = @(c) push(E, p) — the @ wrapper does not
  // capture the assignments.
  EXPECT_EQ(RoutePush(PushSite::kClockedAtProp, false, false),
            PushRouting::kRecurseInner);
}

TEST(Push, ParenthesizedRecursesIntoInner) {
  // §F.4.3: push(E, (p)) = (push(E, p)).
  EXPECT_EQ(RoutePush(PushSite::kParenthesized, false, false),
            PushRouting::kRecurseInner);
}

TEST(Push, NotRecursesIntoInner) {
  // §F.4.3: push(E, not p) = not push(E, p).
  EXPECT_EQ(RoutePush(PushSite::kNot, false, false),
            PushRouting::kRecurseInner);
}

}  // namespace
