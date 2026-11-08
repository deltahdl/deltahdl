#include <gtest/gtest.h>

#include <string>

#include "elaborator/sequence_degeneracy.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string NondegeneracySource(const std::string& spec) {
  return "module m;\n"
         "  logic clk, a, b;\n"
         "  sequence never;\n"
         "    1'b1 intersect (1'b1 ##1 1'b1);\n"
         "  endsequence\n"
         "  assert property (@(posedge clk) " +
         spec +
         ");\n"
         "endmodule\n";
}

TEST(Nondegeneracy, ASequenceAdmittingNoMatchIsRejectedAsAProperty) {
  ElabFixture f;
  Elaborate(NondegeneracySource("1'b1 intersect (1'b1 ##1 1'b1)"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits no match; "
                            "it shall be nondegenerate and admit no empty "
                            "match",
                            6, "16.12.22"));
}

TEST(Nondegeneracy, ASequenceAdmittingOnlyEmptyMatchesIsRejectedAsAProperty) {
  ElabFixture f;
  Elaborate(NondegeneracySource("1'b1[*0]"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits only empty "
                            "matches; it shall be nondegenerate and admit no "
                            "empty match",
                            6, "16.12.22"));
}

TEST(Nondegeneracy, ASequenceAdmittingAnEmptyMatchIsRejectedAsAProperty) {
  ElabFixture f;
  Elaborate(NondegeneracySource("a[*0:2]"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits an empty "
                            "match; it shall be nondegenerate and admit no "
                            "empty match",
                            6, "16.12.22"));
}

TEST(Nondegeneracy, ADegenerateAntecedentOfOverlappingImplicationIsRejected) {
  ElabFixture f;
  Elaborate(NondegeneracySource("1'b1[*0] |-> b"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the antecedent of |-> admits only empty matches; "
                            "it shall be nondegenerate",
                            6, "16.12.22"));
}

TEST(Nondegeneracy,
     AnAntecedentOfNonoverlappingImplicationWithNoMatchIsRejected) {
  ElabFixture f;
  Elaborate(NondegeneracySource("a ##1 never |=> b"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the antecedent of |=> admits no match; it needs "
                            "some match, even an empty one",
                            6, "16.12.22"));
}

TEST(Nondegeneracy, TheUsesTheRestrictionsAllowAreNotReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  assert property (@(posedge clk) a[*0:2] |-> b);\n"
      "  assert property (@(posedge clk) 1'b1[*0] |=> b);\n"
      "  assert property (@(posedge clk) a and a[*2]);\n"
      "  assert property (@(posedge clk) a ##1 b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Nondegeneracy, DegeneracyClassifications) {
  EXPECT_TRUE(IsDegenerate(SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(IsDegenerate(SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsDegenerate(SequenceMatchClass::kAdmitsAtLeastOneNonempty));
  EXPECT_TRUE(IsNondegenerate(SequenceMatchClass::kAdmitsAtLeastOneNonempty));
  EXPECT_FALSE(IsNondegenerate(SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_FALSE(IsNondegenerate(SequenceMatchClass::kAdmitsOnlyEmpty));
}

TEST(Nondegeneracy, RuleAUsedAsPropertyRejectsEmpty) {
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(Nondegeneracy, RuleBOverlappingAntecedentMustBeNondegenerate) {
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
  EXPECT_TRUE(AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_FALSE(
      AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(Nondegeneracy, RuleCNonoverlappingAntecedentAllowsEmptyOnly) {
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
  EXPECT_FALSE(IsDegenerate(SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
  EXPECT_TRUE(IsNondegenerate(SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
  EXPECT_TRUE(
      AdmitsAnyEmptyMatch(SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
}

TEST(Nondegeneracy, RuleARejectsNondegenerateThatAdmitsEmpty) {
  EXPECT_FALSE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
}

TEST(Nondegeneracy, MixedClassLegalAsEitherImplicationAntecedent) {
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kOverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
  EXPECT_TRUE(IsSequenceUsageLegal(
      SequenceUsageContext::kNonoverlappingImplicationAntecedent,
      SequenceMatchClass::kAdmitsBothEmptyAndNonempty));
}

}  // namespace
