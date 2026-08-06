#include <gtest/gtest.h>

#include "elaborator/sequence_degeneracy.h"

using namespace delta;

namespace {

TEST(Nondegeneracy, DegeneracyClassifications) {
  // §16.12.22: degenerate covers (1) sequences that admit no match and (2)
  // sequences that admit only empty matches. Nondegenerate covers sequences
  // that admit at least one nonempty match.
  EXPECT_TRUE(IsDegenerate(SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(IsDegenerate(SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsDegenerate(SequenceMatchClass::kAdmitsAtLeastOneNonempty));
  EXPECT_TRUE(IsNondegenerate(SequenceMatchClass::kAdmitsAtLeastOneNonempty));
  // Negative form of the nondegenerate classifier: both degenerate classes —
  // the one admitting no match and the one admitting only empty matches — are
  // not nondegenerate.
  EXPECT_FALSE(IsNondegenerate(SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_FALSE(IsNondegenerate(SequenceMatchClass::kAdmitsOnlyEmpty));
}

TEST(Nondegeneracy, RuleAUsedAsPropertyRejectsEmpty) {
  // §16.12.22(a): a sequence used as a property shall be nondegenerate and
  // shall not admit any empty match.
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(Nondegeneracy, RuleBOverlappingAntecedentMustBeNondegenerate) {
  // §16.12.22(b): the antecedent of |-> shall be nondegenerate. Both degenerate
  // classes are rejected: a sequence that admits only empty matches, and a
  // sequence that admits no match at all (the clause's own first example,
  // 1'b1 intersect (1'b1 ##1 1'b1)).
  EXPECT_FALSE(IsSequenceUsageLegal(
      SequenceUsageContext::kOverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsSequenceUsageLegal(
      SequenceUsageContext::kOverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kOverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(Nondegeneracy, AdmitsAnyEmptyMatchHelperClassifies) {
  // §16.12.22: the "admits only empty matches" class is the unambiguous
  // empty-match case. The classifier surfaces that membership directly.
  EXPECT_TRUE(AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_FALSE(
      AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(Nondegeneracy, RuleCNonoverlappingAntecedentAllowsEmptyOnly) {
  // §16.12.22(c): the antecedent of |=> shall admit at least one match. A
  // sequence that admits only empty matches is explicitly allowed here.
  EXPECT_FALSE(IsSequenceUsageLegal(
      SequenceUsageContext::kNonoverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kNonoverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kNonoverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(Nondegeneracy, MixedEmptyAndNonemptyIsNondegenerateButAdmitsEmpty) {
  // §16.12.22 cites a[*0:2] as a sequence that admits both an empty match and
  // up to two nonempty matches. It is nondegenerate (it admits a nonempty
  // match) yet it still admits an empty match.
  EXPECT_FALSE(IsDegenerate(SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
  EXPECT_TRUE(IsNondegenerate(SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
  EXPECT_TRUE(
      AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
}

TEST(Nondegeneracy, RuleARejectsNondegenerateThatAdmitsEmpty) {
  // §16.12.22(a): a property sequence shall be nondegenerate AND shall not
  // admit any empty match. The mixed class (e.g. a[*0:2]) is nondegenerate but
  // admits an empty match, so it is illegal as a property — the "shall not
  // admit any empty match" half of the rule, which nondegeneracy alone does
  // not cover.
  EXPECT_FALSE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
}

TEST(Nondegeneracy, MixedClassLegalAsEitherImplicationAntecedent) {
  // §16.12.22(b): an overlapping |-> antecedent need only be nondegenerate, so
  // the mixed class is legal there. §16.12.22(c): a nonoverlapping |=>
  // antecedent need only admit at least one match, so the mixed class is legal
  // there as well. The same sequence that (a) rejects is accepted in both
  // antecedent positions.
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kOverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kNonoverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
}

}  // namespace
