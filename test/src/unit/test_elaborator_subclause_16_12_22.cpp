#include <gtest/gtest.h>

#include <iterator>
#include <string>
#include <vector>

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

constexpr const char* kCheckedPlaces[] = {"module", "generate", "program",
                                          "module property"};

constexpr const char* kUncheckedPlaces[] = {"procedural",    "interface",
                                            "checker",       "package property",
                                            "unit property", "clocking block"};

std::string DegeneracyIn(const std::string& place, const std::string& use) {
  const std::string kDecls =
      "  logic clk; bit a, b; sequence never; 1'b1 intersect (1'b1 ##1 1'b1); "
      "endsequence sequence empty; a[*0]; endsequence sequence opt; "
      "a[*0:2]; endsequence\n";
  const std::string kAssertion =
      "  assert property (@(posedge clk) " + use + ");\n";
  const std::string kDeclared = "  property p; " + use + "; endproperty\n";
  if (place == "procedural") {
    return "module m;\n" + kDecls +
           "  always @(posedge clk) assert property (" + use +
           ");\nendmodule\n";
  }
  if (place == "generate") {
    return "module m;\n" + kDecls + "  if (1) begin : g" +
           kAssertion.substr(1) + "  end\nendmodule\n";
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kDecls + kAssertion + "end" + place + "\n";
  }
  if (place == "module property") {
    return "module m;\n" + kDecls + kDeclared + "endmodule\n";
  }
  if (place == "package property") {
    return "package pk;\n" + kDecls + kDeclared + "endpackage\n";
  }
  if (place == "unit property") return "\n" + kDecls + kDeclared;
  if (place == "clocking block") {
    return "module m;\n" + kDecls +
           "  clocking cb @(posedge clk); property p; " + use +
           "; endproperty endclocking\nendmodule\n";
  }
  return "module m;\n" + kDecls + kAssertion + "endmodule\n";
}

constexpr const char* kPropertyContexts[] = {
    "S",           "not S",     "a |-> S",         "a |=> S",
    "nexttime S",  "always S",  "s_eventually S",  "if (a) S else b",
    "S implies b", "b until S", "S and nexttime b"};

constexpr const char* kStrengthContexts[] = {"strong(S)", "weak(S)"};

std::string InContext(const std::string& context, const std::string& seq) {
  std::string out;
  for (char ch : context) {
    if (ch == 'S') {
      out += seq;
    } else {
      out += ch;
    }
  }
  return out;
}

constexpr const char* kDegenerateAsProperty[] = {
    "1'b1 intersect (1'b1 ##1 1'b1)",
    "a[*0] ##0 b",
    "b ##1 never",
    "never",
    "a[*0]",
    "empty",
    "a[*0:2]",
    "a[*]",
    "opt"};

constexpr const char* kDegenerateWrittenOut[] = {
    "1'b1 intersect (1'b1 ##1 1'b1)",
    "a[*0] ##0 b",
    "b ##1 never",
    "a[*0]",
    "a[*0:2]",
    "a[*]"};

constexpr const char* kDegenerateByName[] = {"never", "empty", "opt"};

void ExpectReportedAsProperty(const std::string& place,
                              const std::string& context,
                              const std::string& seq) {
  const std::string kUse = InContext(context, seq);
  SCOPED_TRACE(place + ": " + kUse);
  ElabFixture f;
  Elaborate(DegeneracyIn(place, kUse), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a sequence used as a property admits", 3,
                            "16.12.22"));
}

TEST(Nondegeneracy,
     ADegenerateOrEmptySequenceAsAPropertyIsReportedInACheckedPlace) {
  for (const char* place : kCheckedPlaces) {
    for (const char* context : kPropertyContexts) {
      for (const char* seq : kDegenerateAsProperty) {
        ExpectReportedAsProperty(place, context, seq);
      }
    }
    for (const char* context : kStrengthContexts) {
      for (const char* seq : kDegenerateWrittenOut) {
        ExpectReportedAsProperty(place, context, seq);
      }
    }
  }
}

TEST(Nondegeneracy,
     DISABLED_ADegenerateOrEmptySequenceAsAPropertyIsReportedInEachOtherPlace) {
  for (const char* place : kUncheckedPlaces) {
    for (const char* context : kPropertyContexts) {
      for (const char* seq : kDegenerateAsProperty) {
        ExpectReportedAsProperty(place, context, seq);
      }
    }
    for (const char* context : kStrengthContexts) {
      for (const char* seq : kDegenerateAsProperty) {
        ExpectReportedAsProperty(place, context, seq);
      }
    }
  }
}

TEST(Nondegeneracy,
     DISABLED_ADegenerateNamedSequenceUnderStrongOrWeakIsReported) {
  for (const char* place : kCheckedPlaces) {
    for (const char* context : kStrengthContexts) {
      for (const char* seq : kDegenerateByName) {
        ExpectReportedAsProperty(place, context, seq);
      }
    }
  }
}

TEST(Nondegeneracy, ADegenerateSequenceIsReportedUnderEachDirective) {
  for (const char* directive : {"cover", "assume"}) {
    for (const char* seq : kDegenerateAsProperty) {
      SCOPED_TRACE(std::string(directive) + " " + seq);
      ElabFixture f;
      Elaborate(
          "module m;\n"
          "  logic clk; bit a, b; sequence never; 1'b1 intersect (1'b1 ##1 "
          "1'b1); endsequence sequence empty; a[*0]; endsequence sequence "
          "opt; a[*0:2]; endsequence\n"
          "  " +
              std::string(directive) + " property (@(posedge clk) " + seq +
              ");\nendmodule\n",
          f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "a sequence used as a property admits", 3,
                                "16.12.22"));
    }
  }
}

constexpr const char* kNondegenerateAsProperty[] = {
    "a ##1 b", "a[*1:2]",       "a and a[*2]",
    "b ##0 a", "a ##1 b[*0:1]", "b ##1 a[*0:1]"};

TEST(Nondegeneracy, ANondegenerateSequenceAsAPropertyIsAcceptedInEachPlace) {
  std::vector<const char*> places(std::begin(kCheckedPlaces),
                                  std::end(kCheckedPlaces));
  places.insert(places.end(), std::begin(kUncheckedPlaces),
                std::end(kUncheckedPlaces));
  for (const char* place : places) {
    std::vector<const char*> contexts(std::begin(kPropertyContexts),
                                      std::end(kPropertyContexts));
    contexts.insert(contexts.end(), std::begin(kStrengthContexts),
                    std::end(kStrengthContexts));
    for (const char* context : contexts) {
      for (const char* seq : kNondegenerateAsProperty) {
        const std::string kUse = InContext(context, seq);
        SCOPED_TRACE(std::string(place) + ": " + kUse);
        ElabFixture f;
        Elaborate(DegeneracyIn(place, kUse), f);
        EXPECT_FALSE(f.has_errors);
      }
    }
  }
}

constexpr const char* kDegenerateOverlappingAntecedents[] = {
    "never |-> b",        "a[*0] |-> b",
    "empty |-> b",        "1'b1 intersect (1'b1 ##1 1'b1) |-> b",
    "a[*0] ##0 b |-> b",  "a |-> empty |-> b",
    "not (empty |-> b)",  "always (never |-> b)",
    "if (a) a[*0] |-> b", "a[*0] #-# b",
    "never #-# b",        "a |-> (empty #-# b)"};

constexpr const char* kUnmatchableNonoverlappingAntecedents[] = {
    "never |=> b",       "a ##1 never |=> b",
    "a[*0] ##0 b |=> b", "1'b1 intersect (1'b1 ##1 1'b1) |=> b",
    "a |-> never |=> b", "always (b ##1 never |=> b)",
    "never #=# b",       "a[*0] ##0 b #=# b"};

void ExpectAntecedentReported(const std::string& place, const std::string& use,
                              const std::string& report) {
  SCOPED_TRACE(place + ": " + use);
  ElabFixture f;
  Elaborate(DegeneracyIn(place, use), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), report, 3, "16.12.22"));
}

TEST(Nondegeneracy,
     ADegenerateAntecedentOfOverlappingImplicationIsReportedInACheckedPlace) {
  for (const char* place : kCheckedPlaces) {
    for (const char* use : kDegenerateOverlappingAntecedents) {
      ExpectAntecedentReported(place, use, "the antecedent of |-> admits");
    }
  }
}

TEST(
    Nondegeneracy,
    DISABLED_ADegenerateAntecedentOfOverlappingImplicationIsReportedInEachOtherPlace) {
  for (const char* place : kUncheckedPlaces) {
    for (const char* use : kDegenerateOverlappingAntecedents) {
      ExpectAntecedentReported(place, use, "the antecedent of |-> admits");
    }
  }
}

TEST(
    Nondegeneracy,
    AnUnmatchableAntecedentOfNonoverlappingImplicationIsReportedInACheckedPlace) {
  for (const char* place : kCheckedPlaces) {
    for (const char* use : kUnmatchableNonoverlappingAntecedents) {
      ExpectAntecedentReported(place, use,
                               "the antecedent of |=> admits no match");
    }
  }
}

TEST(
    Nondegeneracy,
    DISABLED_AnUnmatchableAntecedentOfNonoverlappingImplicationIsReportedInEachOtherPlace) {
  for (const char* place : kUncheckedPlaces) {
    for (const char* use : kUnmatchableNonoverlappingAntecedents) {
      ExpectAntecedentReported(place, use,
                               "the antecedent of |=> admits no match");
    }
  }
}

constexpr const char* kAllowedAntecedents[] = {
    "opt |-> b",       "a[*0:2] |-> b",     "a[*] |-> b",
    "a ##1 b |-> b",   "empty |=> b",       "a[*0] |=> b",
    "opt |=> b",       "a[*0:2] |=> b",     "a ##1 b |=> b",
    "a |-> opt |-> b", "not (empty |=> b)", "always (a[*0] |=> b)",
    "opt #-# b",       "a ##1 b #-# b",     "empty #=# b",
    "a ##1 b #=# b"};

TEST(Nondegeneracy, AnAntecedentTheRestrictionsAllowIsAcceptedInEachPlace) {
  std::vector<const char*> places(std::begin(kCheckedPlaces),
                                  std::end(kCheckedPlaces));
  places.insert(places.end(), std::begin(kUncheckedPlaces),
                std::end(kUncheckedPlaces));
  for (const char* place : places) {
    for (const char* use : kAllowedAntecedents) {
      SCOPED_TRACE(std::string(place) + ": " + use);
      ElabFixture f;
      Elaborate(DegeneracyIn(place, use), f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(Nondegeneracy, DISABLED_ADegenerateParenthesizedGroupIsReported) {
  const std::string kGroup = "(1'b1 intersect (1'b1 ##1 1'b1))";
  for (const char* place : kCheckedPlaces) {
    for (const char* context : kPropertyContexts) {
      ExpectReportedAsProperty(place, context, kGroup);
    }
    for (const char* context : kStrengthContexts) {
      ExpectReportedAsProperty(place, context, kGroup);
    }
    ExpectAntecedentReported(place, kGroup + " |-> b",
                             "the antecedent of |-> admits");
    ExpectAntecedentReported(place, kGroup + " |=> b",
                             "the antecedent of |=> admits no match");
  }
}

constexpr const char* kCoverSequencePlaces[] = {
    "module", "procedural", "generate", "interface", "program", "checker"};

std::string CoverSequenceIn(const std::string& place, const std::string& seq) {
  const std::string kDecls =
      "  logic clk; bit a, b; sequence never; 1'b1 intersect (1'b1 ##1 1'b1); "
      "endsequence sequence empty; a[*0]; endsequence sequence opt; "
      "a[*0:2]; endsequence\n";
  if (place == "procedural") {
    return "module m;\n" + kDecls + "  always @(posedge clk) cover sequence (" +
           seq + ");\nendmodule\n";
  }
  const std::string kCover = "  cover sequence (@(posedge clk) " + seq + ");\n";
  if (place == "generate") {
    return "module m;\n" + kDecls + "  if (1) begin : g" + kCover.substr(1) +
           "  end\nendmodule\n";
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kDecls + kCover + "end" + place + "\n";
  }
  return "module m;\n" + kDecls + kCover + "endmodule\n";
}

constexpr const char* kCoveredDegenerateSequences[] = {
    "a[*0] ##0 b", "1 intersect (1 ##1 1)",
    "a[*0]",       "a[*0:1]",
    "never",       "empty",
    "opt",         "disable iff (b) a[*0]"};

void ExpectCoverSequenceAccepted(const std::string& place) {
  for (const char* seq : kCoveredDegenerateSequences) {
    SCOPED_TRACE(place + ": " + seq);
    ElabFixture f;
    Elaborate(CoverSequenceIn(place, seq), f);
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(Nondegeneracy, ADegenerateCoverSequenceIsAcceptedInAProcedure) {
  ExpectCoverSequenceAccepted("procedural");
}

TEST(Nondegeneracy, DISABLED_ADegenerateCoverSequenceIsAcceptedInEachPlace) {
  for (const char* place : kCoverSequencePlaces) {
    ExpectCoverSequenceAccepted(place);
  }
}

constexpr const char* kGroupsOfEqualLength[] = {
    "(a ##1 b) intersect ((a ##1 b) intersect (a ##1 b))",
    "((a ##1 b) intersect (a ##1 b)) intersect (a ##1 b)",
    "(a ##1 b) intersect ((a ##1 b) or (a ##1 b))",
    "(a ##1 b) intersect ((a ##1 b) and (a ##1 b))",
    "(a ##1 b) intersect ((a ##1 b) within (a ##1 b))",
    "(a ##1 b) within ((a ##1 b) intersect (a ##1 b))"};

constexpr const char* kUngroupedOrUnaffected[] = {
    "(a ##1 b) intersect (a ##1 b) intersect (a ##1 b)",
    "(a ##1 b) and ((a ##1 b) intersect (a ##1 b))",
    "(a ##1 b) intersect (b throughout (a ##1 b))",
    "(a ##1 b) intersect first_match(a ##1 b)",
    "(a ##1 b) intersect ((a ##1 b))"};

void ExpectGroupAccepted(const std::string& place, const std::string& seq) {
  for (const std::string& use :
       {seq, seq + " |-> b", seq + " |=> b", "a |-> " + seq}) {
    SCOPED_TRACE(place);
    SCOPED_TRACE(use);
    ElabFixture f;
    Elaborate(DegeneracyIn(place, use), f);
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(Nondegeneracy, AnUngroupedChainOfEqualLengthIsAcceptedInACheckedPlace) {
  for (const char* place : kCheckedPlaces) {
    for (const char* seq : kUngroupedOrUnaffected) {
      ExpectGroupAccepted(place, seq);
    }
    ExpectGroupAccepted(place, "a ##1 ((b ##1 b) and (b ##1 b ##1 b))");
  }
}

TEST(Nondegeneracy, DISABLED_AGroupOfEqualLengthIsAcceptedInACheckedPlace) {
  for (const char* place : kCheckedPlaces) {
    for (const char* seq : kGroupsOfEqualLength) {
      ExpectGroupAccepted(place, seq);
    }
  }
}

TEST(Nondegeneracy, DISABLED_ANamedSequenceGroupOfEqualLengthIsAccepted) {
  for (const char* seq : kGroupsOfEqualLength) {
    for (const char* place : {"module", "interface", "program", "checker"}) {
      SCOPED_TRACE(std::string(place) + ": " + seq);
      ElabFixture f;
      Elaborate(std::string(place) +
                    " m;\n"
                    "  logic clk; bit a, b;\n"
                    "  sequence g; " +
                    seq +
                    "; endsequence\n"
                    "  cover property (@(posedge clk) g);\n"
                    "end" +
                    place + "\n",
                f);
      EXPECT_FALSE(f.has_errors);
    }
    for (const char* outside : {"package pk;", ""}) {
      SCOPED_TRACE(std::string(outside) + " " + seq);
      const std::string kOutside = outside;
      const std::string kDecl =
          "  sequence g; " + std::string(seq) + "; endsequence\n";
      ElabFixture f;
      std::string src = kOutside.empty() ? "bit a, b;\n" + kDecl
                                         : kOutside + "\n  bit a, b;\n";
      if (!kOutside.empty()) src += kDecl + "endpackage\n";
      src += "module m;\n  logic clk;\n  cover property (@(posedge clk) ";
      src += kOutside.empty() ? "g" : "pk::g";
      src += ");\nendmodule\n";
      Elaborate(src, f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(Nondegeneracy, AnEmptyRepetitionOfAGroupIsReportedAsAProperty) {
  for (const char* place : kCheckedPlaces) {
    SCOPED_TRACE(place);
    ElabFixture f;
    Elaborate(DegeneracyIn(place, "((a ##1 b) or (a ##1 b ##1 b)) [*0:1]"), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a sequence used as a property admits an empty "
                              "match",
                              3, "16.12.22"));
  }
}

}  // namespace
