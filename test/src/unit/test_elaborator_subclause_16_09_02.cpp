#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "common/diagnostic.h"
#include "elaborator/sequence_repetition.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RepetitionCount, ExactCountIsAlwaysWellFormed) {
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeExactCount(0)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeExactCount(3)));
}

TEST(RepetitionCount, FiniteRangeRequiresMinNoGreaterThanMax) {
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeFiniteRange(2, 5)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeFiniteRange(3, 3)));
  EXPECT_FALSE(IsRepetitionCountWellFormed(MakeFiniteRange(5, 2)));
}

TEST(RepetitionCount, DollarRangeIsWellFormed) {
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeDollarRange(0)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeDollarRange(10)));
}

TEST(RepetitionShortcuts, StarAndPlusExpandToDollarRanges) {
  auto star = NormalizeStarShortcut();
  EXPECT_TRUE(star.max_is_dollar);
  EXPECT_EQ(star.min, 0u);

  auto plus = NormalizePlusShortcut();
  EXPECT_TRUE(plus.max_is_dollar);
  EXPECT_EQ(plus.min, 1u);
}

TEST(RepetitionContext, ConsecutiveAllowedOnSequenceAndBoolean) {
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kConsecutive, true, false));
  EXPECT_TRUE(
      IsRepetitionAllowedOn(RepetitionKind::kConsecutive, false, false));
}

TEST(RepetitionContext, GotoAndNonconsecutiveRequireBareBoolean) {
  EXPECT_FALSE(IsRepetitionAllowedOn(RepetitionKind::kGoto, false, false));
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kGoto, true, false));
  EXPECT_FALSE(IsRepetitionAllowedOn(RepetitionKind::kGoto, true, true));
  EXPECT_FALSE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive, true, true));
}

TEST(RepetitionContext, NonconsecutiveRequiresBareBoolean) {
  EXPECT_FALSE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive, false, false));
  EXPECT_TRUE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive, true, false));
}

TEST(RepetitionZero, OnlyConsecutivePermitsZeroIterations) {
  EXPECT_TRUE(IsZeroRepetitionPermitted(RepetitionKind::kConsecutive));
  EXPECT_FALSE(IsZeroRepetitionPermitted(RepetitionKind::kGoto));
  EXPECT_FALSE(IsZeroRepetitionPermitted(RepetitionKind::kNonconsecutive));
}

constexpr char kCount[] =
    "a repetition count shall be a non-negative integer constant expression";

constexpr char kInverted[] =
    "the maximum of a repetition range shall be no less than its minimum";

struct RepetitionPair {
  const char* outside;
  const char* items;
  const char* bad;
  const char* good;
};

std::string Filled(const std::string& text, const std::string& form) {
  std::string out = text;
  size_t at = out.find("@@");
  if (at != std::string::npos) out.replace(at, 2, form);
  return out;
}

std::string RepetitionSource(const RepetitionPair& pair,
                             const std::string& form) {
  return Filled(pair.outside, form) +
         "module m;\n"
         "  bit clk, x, a, b, c;\n"
         "  int v;\n"
         "  " +
         Filled(pair.items, form) + "\nendmodule\n";
}

void ExpectAllowedFormAccepted(const RepetitionPair& pair) {
  SCOPED_TRACE(pair.good);
  const std::string kSrc = RepetitionSource(pair, pair.good);
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

void ExpectPairJudged(const RepetitionPair& pair, const char* message) {
  {
    SCOPED_TRACE(pair.bad);
    const std::string kSrc = RepetitionSource(pair, pair.bad);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(kSrc, pair.bad), "16.9.2"));
  }
  ExpectAllowedFormAccepted(pair);
}

const RepetitionPair kBadCounts[] = {
    {"", "sequence s; @@ ##1 b; endsequence", "a[*-1]", "a[*0]"},
    {"", "sequence s; @@ ##1 b; endsequence", "a[*-1:2]", "a[*0:2]"},
    {"", "sequence s; @@ ##1 c; endsequence", "b[->-1]", "b[->1]"},
    {"", "sequence s; @@ ##1 c; endsequence", "b[=-1:2]", "b[=1:2]"},
    {"", "assert property (@(posedge clk) @@ ##1 b);", "a[*-1]", "a[*0]"},
    {"", "assert property (@(posedge clk) @@ ##1 c);", "b[->-1]", "b[->1]"},
    {"", "@@; sequence s; a[*P] ##1 b; endsequence", "localparam int P = -1",
     "localparam int P = 0"},
    {"", "localparam int N = 2; sequence s; @@ ##1 b; endsequence", "a[*v]",
     "a[*N]"},
    {"",
     "localparam int N = 2; sequence s; int w; (1, w = 2) ##1 @@ ##1 b; "
     "endsequence",
     "a[*w]", "a[*N]"},
    {"", "sequence s; @@ ##1 b; endsequence", "a[*2.5]", "a[*2]"},
    {"",
     "localparam real R = 2.0; localparam int I = 2; sequence s; @@ ##1 b; "
     "endsequence",
     "a[*R]", "a[*I]"},
    {"",
     "sequence s(int k); a[*k] ##1 b; endsequence\n"
     "  cover property (@(posedge clk) @@);",
     "s(-1)", "s(0)"},
    {"",
     "sequence u(k); a[*k] ##1 b; endsequence\n"
     "  cover property (@(posedge clk) @@);",
     "u(2.5)", "u(2)"}};

TEST(RepetitionCountRule, DISABLED_ACountThatIsNoNonNegativeIntegerIsReported) {
  for (const auto& pair : kBadCounts) ExpectPairJudged(pair, kCount);
}

TEST(RepetitionCountRule, ANonNegativeIntegerConstantCountIsAccepted) {
  for (const auto& pair : kBadCounts) ExpectAllowedFormAccepted(pair);
}

const RepetitionPair kInvertedRanges[] = {
    {"", "sequence s; @@ ##1 b; endsequence", "a[*3:1]", "a[*3:3]"},
    {"", "assert property (@(posedge clk) @@ ##1 b);", "a[*3:1]", "a[*3:3]"},
    {"", "property p; @@ |-> b; endproperty", "a[*3:1]", "a[*1:3]"},
    {"", "sequence s; @@ ##1 c; endsequence", "(a ##1 b)[*3:1]",
     "(a ##1 b)[*1:3]"},
    {"", "sequence ab; a ##1 b; endsequence sequence s; @@ ##1 c; endsequence",
     "ab[*3:1]", "ab[*1:3]"},
    {"", "localparam int @@; sequence s; a[*M:N] ##1 b; endsequence",
     "M = 3, N = 1", "M = 1, N = 3"},
    {"", "sequence s; @@ ##1 c; endsequence", "b[->3:1]", "b[->1:3]"},
    {"", "sequence s; @@ ##1 c; endsequence", "b[=3:1]", "b[=1:3]"},
    {"",
     "sequence s(int lo, int hi); a[*lo:hi] ##1 b; endsequence\n"
     "  cover property (@(posedge clk) @@);",
     "s(3, 1)", "s(1, 3)"}};

TEST(RepetitionRangeRule, DISABLED_AMinimumAboveTheMaximumIsReported) {
  for (const auto& pair : kInvertedRanges) ExpectPairJudged(pair, kInverted);
}

TEST(RepetitionRangeRule, AMinimumNoGreaterThanTheMaximumIsAccepted) {
  for (const auto& pair : kInvertedRanges) ExpectAllowedFormAccepted(pair);
}

RepetitionPair InPlace(const char* place) {
  const std::string kPlace = place;
  if (kPlace == "interface") {
    return {
        "interface ifc;\n  bit a, b;\n  sequence s; @@ ##1 b; endsequence\n"
        "endinterface\n",
        "ifc i();", "", ""};
  }
  if (kPlace == "program") {
    return {
        "program pg;\n  bit a, b;\n  sequence s; @@ ##1 b; endsequence\n"
        "endprogram\n",
        "", "", ""};
  }
  if (kPlace == "checker") {
    return {
        "checker ck(a, b);\n  sequence s; @@ ##1 b; endsequence\n"
        "endchecker\n",
        "ck k(a, b);", "", ""};
  }
  if (kPlace == "package") {
    return {
        "package pk;\n  sequence s(a, b); @@ ##1 b; endsequence\n"
        "endpackage\n",
        "cover property (@(posedge clk) pk::s(a, b));", "", ""};
  }
  if (kPlace == "generate block") {
    return {"",
            "if (1) begin : g\n    sequence s; @@ ##1 b; endsequence\n  end",
            "", ""};
  }
  return {"sequence s(a, b); @@ ##1 b; endsequence\n",
          "cover property (@(posedge clk) s(a, b));", "", ""};
}

const char* const kRepetitionPlaces[] = {"interface",      "program",
                                         "checker",        "package",
                                         "generate block", "compilation unit"};

void ExpectJudgedInEveryPlace(const char* bad, const char* good,
                              const char* message) {
  for (const char* place : kRepetitionPlaces) {
    SCOPED_TRACE(place);
    RepetitionPair pair = InPlace(place);
    pair.bad = bad;
    pair.good = good;
    ExpectPairJudged(pair, message);
  }
}

void ExpectAcceptedInEveryPlace(const char* good) {
  for (const char* place : kRepetitionPlaces) {
    SCOPED_TRACE(place);
    RepetitionPair pair = InPlace(place);
    pair.good = good;
    ExpectAllowedFormAccepted(pair);
  }
}

TEST(RepetitionCountRule, DISABLED_ANegativeCountIsReportedInEveryPlace) {
  ExpectJudgedInEveryPlace("a[*-1]", "a[*0]", kCount);
}

TEST(RepetitionRangeRule, DISABLED_AnInvertedRangeIsReportedInEveryPlace) {
  ExpectJudgedInEveryPlace("a[*3:1]", "a[*1:3]", kInverted);
}

TEST(RepetitionRangeRule, AnOrderedRangeIsAcceptedInEveryPlace) {
  ExpectAcceptedInEveryPlace("a[*1:3]");
  ExpectAcceptedInEveryPlace("a[*0]");
}

TEST(RepetitionCountRule, AZeroCountOnGotoAndNonconsecutiveIsAccepted) {
  for (const char* form : {"b[->0]", "b[=0]", "b[->0:2]", "b[=0:$]"}) {
    ExpectAllowedFormAccepted(
        {"", "sequence s; x ##1 @@ ##1 c; endsequence", "", form});
  }
}

}  // namespace
