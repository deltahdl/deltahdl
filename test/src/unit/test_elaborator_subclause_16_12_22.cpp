#include <gtest/gtest.h>

#include <string>

#include "elaborator/sequence_degeneracy.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The module of test/src/e2e/nondegenerate_sequences.sv around one
// assertion: never, the clause's sequence whose operands can have no length
// in common, is declared beside it.
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

// §16.12.22 (a): a sequence used as a property shall be nondegenerate: the
// clause's 1'b1 intersect (1'b1 ##1 1'b1) admits no match, its operands
// one and two ticks long.
TEST(Nondegeneracy, ASequenceAdmittingNoMatchIsRejectedAsAProperty) {
  ElabFixture f;
  Elaborate(NondegeneracySource("1'b1 intersect (1'b1 ##1 1'b1)"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits no match; "
                            "it shall be nondegenerate and admit no empty "
                            "match",
                            6, "16.12.22"));
}

// §16.12.22 (a): the clause's 1'b1[*0] admits only the empty match, and is
// degenerate too.
TEST(Nondegeneracy, ASequenceAdmittingOnlyEmptyMatchesIsRejectedAsAProperty) {
  ElabFixture f;
  Elaborate(NondegeneracySource("1'b1[*0]"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits only empty "
                            "matches; it shall be nondegenerate and admit no "
                            "empty match",
                            6, "16.12.22"));
}

// §16.12.22 (a): the clause's a[*0:2] is nondegenerate, admitting up to two
// nonempty matches, but admits an empty match, which a sequence used as a
// property shall not.
TEST(Nondegeneracy, ASequenceAdmittingAnEmptyMatchIsRejectedAsAProperty) {
  ElabFixture f;
  Elaborate(NondegeneracySource("a[*0:2]"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits an empty "
                            "match; it shall be nondegenerate and admit no "
                            "empty match",
                            6, "16.12.22"));
}

// §16.12.22 (b): the antecedent of |-> shall be nondegenerate.
TEST(Nondegeneracy, ADegenerateAntecedentOfOverlappingImplicationIsRejected) {
  ElabFixture f;
  Elaborate(NondegeneracySource("1'b1[*0] |-> b"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the antecedent of |-> admits only empty matches; "
                            "it shall be nondegenerate",
                            6, "16.12.22"));
}

// §16.12.22 (c): the antecedent of |=> shall admit at least one match; an
// instance of never among its operands leaves it none.
TEST(Nondegeneracy,
     AnAntecedentOfNonoverlappingImplicationWithNoMatchIsRejected) {
  ElabFixture f;
  Elaborate(NondegeneracySource("a ##1 never |=> b"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the antecedent of |=> admits no match; it shall "
                            "admit at least one match",
                            6, "16.12.22"));
}

// §16.12.22 (b) and (c): a sequence admitting an empty match beside
// nonempty ones may be the antecedent of |->, one admitting only empty
// matches the antecedent of |=>, and a sequence admitting nonempty matches
// alone a property; none is reported.
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
