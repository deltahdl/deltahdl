#include <gtest/gtest.h>

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/multiclock_sequence.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string RulesSource(const std::string& spec) {
  return "module m;\n"
         "  logic clk0, clk1, clk2, sig0, sig1, s1, s2;\n"
         "  assert property (" +
         spec +
         ");\n"
         "endmodule\n";
}

std::string ClockPlaces(const std::string& body) {
  return "module m;\n"
         "  logic clk0, clk1, sig0, sig1;\n"
         "  sequence sc0; @(posedge clk0) sig0 ##1 sig1; endsequence "
         "sequence sc1; @(posedge clk1) sig0 ##1 sig1; endsequence\n"
         "  sequence r; @(posedge clk0) " +
         body +
         "; endsequence\n"
         "  property q; @(posedge clk0) " +
         body +
         "; endproperty\n"
         "  assert property (@(posedge clk0) " +
         body +
         ");\n"
         "endmodule\n";
}

TEST(MulticlockSequenceLegality, AnEmptyMatchingSubsequenceIsReported) {
  ElabFixture f;
  Elaborate(RulesSource("@(posedge clk0) sig0 ##1 @(posedge clk1) sig1[*0:1]"),
            f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a maximal singly clocked subsequence of a "
                            "multiclocked sequence may not match the empty "
                            "word",
                            3, "16.13.1"));
}

TEST(MulticlockSequenceLegality,
     ADelayOtherThanOneOrZeroAcrossClocksIsReported) {
  ElabFixture f;
  Elaborate(RulesSource("@(posedge clk1) s1 ##2 @(posedge clk2) s2"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "differently clocked sequence operands may be "
                            "joined only by the single-delay (##1) or "
                            "zero-delay (##0) operator",
                            3, "16.13.1"));
}

TEST(MulticlockSequenceLegality, AnIntersectOverDifferentClocksIsReported) {
  ElabFixture f;
  Elaborate(RulesSource("@(posedge clk1) s1 intersect @(posedge clk2) s2"), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "differently clocked sequence operands may be "
                            "joined only by the single-delay (##1) or "
                            "zero-delay (##0) operator, not by intersect",
                            3, "16.13.1"));
}

TEST(MulticlockSequenceLegality, TheJoinsTheClauseAllowsAreNotReported) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk0, clk1, sig0, sig1, s1, s2;\n"
      "  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1);\n"
      "  assert property (@(posedge clk0) sig0 ##0 @(posedge clk1) sig1);\n"
      "  assert property (@(posedge clk1) s1 ##2 @(posedge clk1) s2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MulticlockSequenceLegality, SinglyClockedSequenceIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk", MulticlockJoin::kLeading, true},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, DifferentlyClockedNonemptyJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kSingleDelay, false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, EmptyMatchingTrailingSubsequenceIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kSingleDelay, true},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

TEST(MulticlockSequenceLegality, EmptyMatchingLeadingSubsequenceIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, true},
      {"clk2", MulticlockJoin::kSingleDelay, false},
  };
  EXPECT_TRUE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, DifferentlyClockedZeroDelayJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kZeroDelay, false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, DifferentlyClockedOtherJoinIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kOther, false},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

TEST(MulticlockSequenceLegality, IdenticallyClockedOtherJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk", MulticlockJoin::kLeading, false},
      {"clk", MulticlockJoin::kOther, false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, MultipleClockBoundariesNonemptyJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kSingleDelay, false},
      {"clk3", MulticlockJoin::kZeroDelay, false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, EmptyMatchingInteriorSubsequenceIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kSingleDelay, true},
      {"clk3", MulticlockJoin::kSingleDelay, false},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

TEST(MulticlockSequenceLegality, SameClockOtherJoinWithinMulticlockIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk1", MulticlockJoin::kOther, false},
      {"clk2", MulticlockJoin::kSingleDelay, false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, SameClockChainWithEmptyMatchIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk", MulticlockJoin::kLeading, false},
      {"clk", MulticlockJoin::kSingleDelay, true},
      {"clk", MulticlockJoin::kSingleDelay, false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

TEST(MulticlockSequenceLegality, CrossClockOtherJoinInInteriorIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {"clk1", MulticlockJoin::kLeading, false},
      {"clk2", MulticlockJoin::kSingleDelay, false},
      {"clk3", MulticlockJoin::kOther, false},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

TEST(MulticlockSequenceLegality, ARepeatedSequenceOnAnotherClockIsReported) {
  for (const char* body :
       {"(@(posedge clk1) sig0 ##1 sig1)[*2]",
        "(@(posedge clk1) sig0 ##1 sig1)[*1:2]", "(@(posedge clk1) sig0)[*2]",
        "(@(posedge clk1) sig0 and sig1)[*2]",
        "(sig0 ##1 @(posedge clk1) sig1)[*2]", "sc1[*2]"}) {
    ElabFixture f;
    Elaborate(ClockPlaces(body), f);
    for (int line : {4, 5, 6}) {
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "a repeated sequence may name no clocking "
                                "event other than the one in force where it "
                                "is written",
                                line, "F.3.2"))
          << body << " at line " << line;
    }
  }
}

TEST(MulticlockSequenceLegality, ARepeatedSequenceOnTheClockInForceIsLegal) {
  for (const char* body :
       {"(@(posedge clk0) sig0 ##1 sig1)[*2]",
        "(@(posedge clk0) sig0 ##1 sig1)[*1:2]", "(@(posedge clk0) sig0)[*2]",
        "(@(posedge clk0) sig0 and sig1)[*2]", "sc0[*2]",
        "sig0 ##1 @(posedge clk1) (sig1 ##1 sig0)[*2]",
        "sig0 ##1 @(posedge clk1) (@(posedge clk1) sig1 ##1 sig0)[*2]"}) {
    ElabFixture f;
    auto* design = ElaborateSrc(ClockPlaces(body), f);
    EXPECT_NE(design, nullptr) << body;
    EXPECT_FALSE(f.has_errors) << body;
  }
}

TEST(MulticlockSequenceLegality, AFirstOperandOnAnotherClockIsReported) {
  for (const auto& [body, op] :
       std::vector<std::pair<std::string, std::string>>{
           {"(@(posedge clk1) sig0 ##1 sig1) within (sig0 ##1 sig1 ##1 sig0)",
            "within"},
           {"(@(posedge clk1) sig0 ##1 sig1) intersect (sig1 ##1 sig0)",
            "intersect"},
           {"(@(posedge clk1) sig0 ##1 sig1) and (sig1 ##1 sig0)", "and"},
           {"(@(posedge clk1) sig0 ##1 sig1) or (sig1 ##1 sig0)", "or"}}) {
    ElabFixture f;
    Elaborate(ClockPlaces(body), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "differently clocked sequence operands may be "
                              "joined only by the single-delay (##1) or "
                              "zero-delay (##0) operator, not by " +
                                  op,
                              4, "16.13.1"))
        << body;
  }
}

TEST(MulticlockSequenceLegality, AFirstOperandOnTheClockInForceIsLegal) {
  for (const char* body :
       {"(@(posedge clk0) sig0 ##1 sig1) within (sig0 ##1 sig1 ##1 sig0)",
        "(@(posedge clk0) sig0 ##1 sig1) intersect (sig1 ##1 sig0)",
        "(@(posedge clk0) sig0 ##1 sig1) and (sig1 ##1 sig0)",
        "(@(posedge clk0) sig0 ##1 sig1) or (sig1 ##1 sig0)"}) {
    ElabFixture f;
    auto* design = ElaborateSrc(ClockPlaces(body), f);
    EXPECT_NE(design, nullptr) << body;
    EXPECT_FALSE(f.has_errors) << body;
  }
}

}  // namespace
