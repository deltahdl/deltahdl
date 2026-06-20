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
  // §16.12.22(b): the antecedent of |-> shall be nondegenerate.
  EXPECT_FALSE(IsSequenceUsageLegal(
      SequenceUsageContext::kOverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsOnlyEmpty));
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

}  // namespace
