#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
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

constexpr const char* kJoinedOnlyByDelays =
    "differently clocked sequence operands may be joined only by the "
    "single-delay (##1) or zero-delay (##0) operator";
constexpr const char* kEmptyWord =
    "a maximal singly clocked subsequence of a multiclocked sequence may not "
    "match the empty word";

constexpr const char* kDesignUnitPlaces[] = {"module", "generate", "interface",
                                             "program", "checker"};
constexpr const char* kPackageAndUnitPlaces[] = {"package", "unit"};
constexpr const char* kEveryMulticlockPlace[] = {
    "module", "generate", "interface", "program", "checker", "package", "unit"};

std::string MulticlockPlaced(const std::string& place,
                             const std::string& declarations,
                             const std::string& assertions) {
  std::string signals = "  logic clk0, clk1, clk2, a, b, c;\n";
  std::string ports = "clk0, clk1, clk2, a, b, c";
  if (place == "module") {
    return "module m;\n" + signals + declarations + assertions + "endmodule\n";
  }
  if (place == "generate") {
    return "module m;\n" + signals + "  if (1) begin : g\n" + declarations +
           assertions + "  end\nendmodule\n";
  }
  std::string top =
      "module m;\n" + signals + "  w u(" + ports + ");\nendmodule\n";
  if (place == "interface" || place == "program") {
    return place + " w(input logic " + ports + ");\n" + declarations +
           assertions + "end" + place + "\n" + top;
  }
  if (place == "checker") {
    return "checker w(" + ports + ");\n" + declarations + assertions +
           "endchecker\n" + top;
  }
  if (place == "package") {
    return "package pk;\n" + signals + declarations +
           "endpackage\nmodule m;\n  import pk::*;\n" + assertions +
           "endmodule\n";
  }
  return signals + declarations + "module m;\n" + assertions + "endmodule\n";
}

std::string BodyInEachForm(const std::string& place, const std::string& body) {
  return MulticlockPlaced(
      place,
      "  sequence se; b[*0:1]; endsequence\n"
      "  sequence sn; b[*1:2]; endsequence\n"
      "  sequence sp(x); x; endsequence\n"
      "  sequence sd; @(posedge clk0) " +
          body + "; endsequence\n  property pd; @(posedge clk0) " + body +
          "; endproperty\n",
      "  assert property (@(posedge clk0) " + body + ");\n");
}

size_t ErrorsAt(const std::vector<Diagnostic>& diags, uint32_t line) {
  size_t count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line) {
      ++count;
    }
  }
  return count;
}

::testing::AssertionResult ReportedOnlyOnce(
    const std::vector<Diagnostic>& diags, const std::string& message,
    uint32_t line) {
  ::testing::AssertionResult reported =
      ReportedError(diags, message, line, "16.13.1");
  if (!reported) return reported;
  size_t count = ErrorsAt(diags, line);
  if (count == 1) return ::testing::AssertionSuccess();
  return ::testing::AssertionFailure()
         << count << " errors stand at line " << line << " where one should";
}

struct ForbiddenBody {
  std::string body;
  std::string message;
  bool sequence_only = false;
};

std::string JoinedBy(const std::string& op) {
  return std::string(kJoinedOnlyByDelays) + ", not by " + op;
}

std::string OnTheClockInForce(std::string body) {
  for (size_t at = body.find("clk1"); at != std::string::npos;
       at = body.find("clk1", at)) {
    body.replace(at, 4, "clk0");
  }
  return body;
}

void ExpectAcceptedIn(const std::string& place, const std::string& body) {
  SCOPED_TRACE(place + ": " + body);
  ElabFixture f;
  std::string src = BodyInEachForm(place, body);
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_EQ(f.diag.ErrorCount(), 0u) << src;
}

void ExpectReportedIn(const std::string& place, const ForbiddenBody& row) {
  SCOPED_TRACE(place + ": " + row.body);
  ElabFixture f;
  std::string src = BodyInEachForm(place, row.body);
  ElaborateSrc(src, f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedOnlyOnce(diags, row.message, LineHolding(src, "sequence sd;")));
  if (row.sequence_only) return;
  EXPECT_TRUE(
      ReportedOnlyOnce(diags, row.message, LineHolding(src, "property pd;")));
  EXPECT_TRUE(ReportedOnlyOnce(diags, row.message,
                               LineHolding(src, "assert property (@(posedge")));
}

template <typename Places>
void ExpectRowsJudgedIn(const Places& places,
                        const std::vector<ForbiddenBody>& rows) {
  for (const char* place : places) {
    for (const ForbiddenBody& row : rows) {
      ExpectReportedIn(place, row);
      ExpectAcceptedIn(place, OnTheClockInForce(row.body));
    }
  }
}

std::vector<ForbiddenBody> DelayJoinsAcrossClocks() {
  std::vector<ForbiddenBody> rows;
  for (const char* body :
       {"a ##3 @(posedge clk1) b", "a ##[1:2] @(posedge clk1) b",
        "a ##[0:1] @(posedge clk1) b", "a ##[*] @(posedge clk1) b",
        "a ##[+] @(posedge clk1) b",
        "a ##1 @(posedge clk1) b ##2 @(posedge clk0) c",
        "(a ##1 @(posedge clk1) b) ##2 c"}) {
    rows.push_back({body, kJoinedOnlyByDelays});
  }
  return rows;
}

std::vector<ForbiddenBody> OperatorsAcrossClocks() {
  return {
      {"(c ##1 b) intersect (a ##1 @(posedge clk1) b)", JoinedBy("intersect")},
      {"(a ##1 b) intersect (@(posedge clk1) b ##1 c)", JoinedBy("intersect")},
      {"(@(posedge clk1) a ##1 b) intersect (b ##1 c)", JoinedBy("intersect")},
      {"(a ##1 @(posedge clk1) b) and c", JoinedBy("and"), true},
      {"(a ##1 @(posedge clk1) b) or c", JoinedBy("or"), true},
      {"(a ##1 b) and (@(posedge clk1) b ##1 c)", JoinedBy("and"), true},
      {"(a ##1 b) or (@(posedge clk1) b ##1 c)", JoinedBy("or"), true}};
}

std::vector<ForbiddenBody> WithinAcrossClocks() {
  return {
      {"(@(posedge clk1) a ##1 b) within (b ##1 c ##1 a)", JoinedBy("within")},
      {"(a ##1 b) within (@(posedge clk1) b ##1 c ##1 a)", JoinedBy("within")},
      {"(a ##1 b) within (b ##1 @(posedge clk1) c ##1 a)", JoinedBy("within")}};
}

std::vector<ForbiddenBody> ThroughoutAndFirstMatchAcrossClocks() {
  return {{"a throughout (@(posedge clk1) b ##1 c)", JoinedBy("throughout")},
          {"a throughout (b ##1 @(posedge clk1) c)", JoinedBy("throughout")},
          {"first_match(@(posedge clk1) b ##1 c)", JoinedBy("first_match")},
          {"first_match(b ##1 @(posedge clk1) c)", JoinedBy("first_match")}};
}

std::vector<ForbiddenBody> NestedOperatorsAcrossClocks() {
  return {
      {"a ##1 ((@(posedge clk1) a ##1 b) intersect (b ##1 c))",
       JoinedBy("intersect")},
      {"a ##1 ((@(posedge clk1) a ##1 b) within (b ##1 c ##1 a))",
       JoinedBy("within")},
      {"a ##1 ((@(posedge clk1) a ##1 b) and (b ##1 c))", JoinedBy("and")},
      {"a ##1 ((@(posedge clk1) a ##1 b) or (b ##1 c))", JoinedBy("or")},
      {"a ##1 (c throughout (@(posedge clk1) a ##1 b))",
       JoinedBy("throughout")},
      {"a ##1 first_match(@(posedge clk1) a ##1 b)", JoinedBy("first_match")},
      {"a ##1 (b ##1 ((@(posedge clk1) a ##1 b) intersect (b ##1 c)))",
       JoinedBy("intersect")},
      {"a ##1 (b ##1 (c throughout (@(posedge clk1) a ##1 b)))",
       JoinedBy("throughout")}};
}

TEST(MulticlockSequenceLegality,
     ADelayOtherThanOneOrZeroAcrossClocksIsReportedOnceInEachDesignUnit) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, DelayJoinsAcrossClocks());
}

TEST(MulticlockSequenceLegality,
     AnOperatorOverDifferentClocksIsReportedOnceInEachDesignUnit) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, OperatorsAcrossClocks());
}

TEST(MulticlockSequenceLegality,
     DISABLED_AWithinOverDifferentClocksIsReportedOnceNamingWithin) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, WithinAcrossClocks());
}

TEST(MulticlockSequenceLegality,
     DISABLED_AThroughoutOrFirstMatchOverDifferentClocksIsReported) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, ThroughoutAndFirstMatchAcrossClocks());
}

TEST(MulticlockSequenceLegality,
     DISABLED_AnOperatorOverDifferentClocksNestedInAGroupIsReported) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, NestedOperatorsAcrossClocks());
}

TEST(MulticlockSequenceLegality,
     DISABLED_AJoinAcrossClocksInAPackageOrUnitDeclarationIsReported) {
  for (const auto& rows : {DelayJoinsAcrossClocks(), OperatorsAcrossClocks()}) {
    ExpectRowsJudgedIn(kPackageAndUnitPlaces, rows);
  }
}

struct InstancedSequence {
  std::string declaration;
  std::string instance;
  std::string message;
};

void ExpectInstanceJudgedIn(const std::string& place,
                            const InstancedSequence& row) {
  SCOPED_TRACE(place + ": " + row.declaration + " / " + row.instance);
  std::string assertion = "  assert property (" + row.instance + ");\n";
  ElabFixture f;
  std::string src =
      MulticlockPlaced(place, "  " + row.declaration + "\n", assertion);
  ElaborateSrc(src, f);
  if (row.message.empty()) {
    EXPECT_EQ(f.diag.ErrorCount(), 0u) << src;
    return;
  }
  EXPECT_TRUE(ReportedOnlyOnce(f.diag.Diagnostics(), row.message,
                               LineHolding(src, "assert property (")))
      << src;
  EXPECT_EQ(f.diag.ErrorCount(), 1u) << src;
}

void ExpectInstancesJudgedInEachPlace(
    const std::vector<InstancedSequence>& rows) {
  for (const char* place : kEveryMulticlockPlace) {
    for (const InstancedSequence& row : rows)
      ExpectInstanceJudgedIn(place, row);
  }
}

TEST(MulticlockSequenceLegality,
     DISABLED_AnUnclockedSequenceIsJudgedUnderTheClockInForceAtItsInstance) {
  const std::string kInForce = "@(posedge clk0) t";
  ExpectInstancesJudgedInEachPlace({
      {"sequence t; (@(posedge clk1) a ##1 b) intersect (b ##1 c); "
       "endsequence",
       kInForce, JoinedBy("intersect")},
      {"sequence t; (@(posedge clk1) a ##1 b) within (b ##1 c ##1 a); "
       "endsequence",
       kInForce, JoinedBy("within")},
      {"sequence t; (@(posedge clk1) a ##1 b) and (b ##1 c); endsequence",
       kInForce, JoinedBy("and")},
      {"sequence t; (@(posedge clk1) a ##1 b) or (b ##1 c); endsequence",
       kInForce, JoinedBy("or")},
      {"sequence t; c throughout (@(posedge clk1) a ##1 b); endsequence",
       kInForce, JoinedBy("throughout")},
      {"sequence t; (@(posedge clk0) a ##1 b) intersect (b ##1 c); "
       "endsequence",
       kInForce, ""},
      {"sequence t; (@(posedge clk0) a ##1 b) within (b ##1 c ##1 a); "
       "endsequence",
       kInForce, ""},
  });
}

TEST(MulticlockSequenceLegality,
     DISABLED_ClockFormalsAreJudgedAfterTheirActualsAreSubstituted) {
  const std::string kDelay =
      "sequence ms(c0, c1, x, y); @(posedge c0) x ##2 @(posedge c1) y; "
      "endsequence";
  const std::string kIntersect =
      "sequence ms(c0, c1, x, y); (@(posedge c0) x ##1 y) intersect "
      "(@(posedge c1) y ##1 x); endsequence";
  const std::string kEvents =
      "sequence ms(event c0, event c1, untyped x, untyped y); @c0 x ##2 @c1 "
      "y; endsequence";
  ExpectInstancesJudgedInEachPlace({
      {kDelay, "ms(clk0, clk1, a, b)", kJoinedOnlyByDelays},
      {kDelay, "ms(clk0, clk0, a, b)", ""},
      {kIntersect, "ms(clk0, clk1, a, b)", JoinedBy("intersect")},
      {kIntersect, "ms(clk0, clk0, a, b)", ""},
      {kEvents, "ms(posedge clk0, posedge clk1, a, b)", kJoinedOnlyByDelays},
      {kEvents, "ms(posedge clk0, posedge clk0, a, b)", ""},
  });
}

std::vector<ForbiddenBody> EmptyMatchingRepetitions() {
  std::vector<ForbiddenBody> rows;
  for (const char* body :
       {"a ##1 @(posedge clk1) b[*0:1]", "a ##0 @(posedge clk1) b[*0:$]",
        "a[*0:1] ##1 @(posedge clk1) b",
        "a ##1 @(posedge clk1) b[*0:1] ##1 @(posedge clk2) c",
        "a ##1 @(posedge clk1) b[*0]", "a ##1 @(posedge clk1) b[*0:2]",
        "a ##1 @(posedge clk1) b[=0]", "a ##1 @(posedge clk1) b[=0:1]",
        "a ##1 @(posedge clk1) b[->0:1]", "a ##1 @(posedge clk1) (b[*0:1])",
        "a ##1 @(posedge clk1) (b ##1 c)[*0:1]",
        "a ##1 @(posedge clk1) b[*0:1] ##1 c[*0:1]",
        "a ##1 @(posedge clk1) (c throughout b[*0:1])",
        "a ##1 @(posedge clk1) se"}) {
    rows.push_back({body, kEmptyWord});
  }
  return rows;
}

std::vector<ForbiddenBody> EmptyMatchingOperators() {
  std::vector<ForbiddenBody> rows;
  for (const char* body : {"a ##1 @(posedge clk1) (b[*0:1] or c)",
                           "a ##1 @(posedge clk1) (c or b[*0])",
                           "a ##1 @(posedge clk1) (b[*0:1] or c[*0])",
                           "(a[*0:1] or b) ##1 @(posedge clk1) c",
                           "a ##1 @(posedge clk1) (b[*0:1] and c[*0:1])",
                           "a ##1 @(posedge clk1) (b[*0:1] intersect c[*0:1])",
                           "a ##1 @(posedge clk1) (b[*0:1] within c[*0:1])",
                           "a ##1 @(posedge clk1) first_match(b[*0:1])",
                           "a ##1 @(posedge clk1) ((b[*0:1]))",
                           "a ##1 @(posedge clk1) (b[*0:1])[*1:2]",
                           "a ##1 @(posedge clk1) sp(b[*0:1])"}) {
    rows.push_back({body, kEmptyWord});
  }
  return rows;
}

constexpr const char* kNonemptyStretches[] = {
    "a ##1 @(posedge clk1) b",
    "a ##0 @(posedge clk1) b[*1:$]",
    "a[*1:2] ##1 @(posedge clk1) b",
    "a ##1 @(posedge clk1) b[*1:2] ##1 @(posedge clk2) c",
    "a ##1 @(posedge clk1) b[*1]",
    "a ##1 @(posedge clk1) b[*1:2]",
    "a ##1 @(posedge clk1) b[=1:2]",
    "a ##1 @(posedge clk1) b[->1:2]",
    "a ##1 @(posedge clk1) (b[*1:2])",
    "a ##1 @(posedge clk1) (b ##1 c)[*1:2]",
    "a ##1 @(posedge clk1) b[*0:1] ##1 c",
    "a ##1 @(posedge clk1) (c throughout b[*1:2])",
    "a ##1 @(posedge clk1) sn",
    "a ##1 @(posedge clk1) (b[*1:2] or c)",
    "(a[*1:2] or b) ##1 @(posedge clk1) c",
    "a ##1 @(posedge clk1) (b[*0:1] and c)",
    "a ##1 @(posedge clk1) (b[*0:1] intersect c)",
    "a ##1 @(posedge clk1) (b[*0:1] within c[*1:2])",
    "a ##1 @(posedge clk1) first_match(b[*1:2])",
    "a ##1 @(posedge clk1) ((b[*1:2]))",
    "a ##1 @(posedge clk1) (b[*1:2])[*1:2]",
    "a ##1 @(posedge clk1) sp(b[*1:2])",
    "a ##1 @(posedge clk1) (b[*0:1] ##0 b[*0:1])",
    "a ##1 @(posedge clk1) ##[0:1] b"};

TEST(MulticlockSequenceLegality,
     ARepetitionAdmittingAnEmptyMatchIsReportedOnceInEachDesignUnit) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, EmptyMatchingRepetitions());
}

TEST(MulticlockSequenceLegality,
     DISABLED_AnOperatorAdmittingAnEmptyMatchIsReportedInEachDesignUnit) {
  ExpectRowsJudgedIn(kDesignUnitPlaces, EmptyMatchingOperators());
}

TEST(MulticlockSequenceLegality,
     DISABLED_AnEmptyMatchInAPackageOrUnitDeclarationIsReported) {
  for (const auto& rows :
       {EmptyMatchingRepetitions(), EmptyMatchingOperators()}) {
    ExpectRowsJudgedIn(kPackageAndUnitPlaces, rows);
  }
}

TEST(MulticlockSequenceLegality, AStretchAdmittingNoEmptyMatchIsAccepted) {
  for (const char* place : kEveryMulticlockPlace) {
    for (const char* body : kNonemptyStretches) {
      ExpectAcceptedIn(place, body);
    }
  }
}

TEST(MulticlockSequenceLegality,
     DISABLED_AnEmptyMatchUnderClockFormalsIsJudgedAfterSubstitution) {
  const std::string kTrailing =
      "sequence me(c0, c1, x, y); @(posedge c0) x ##1 @(posedge c1) "
      "y[*0:1]; endsequence";
  const std::string kAlternative =
      "sequence me(c0, c1, x, y); @(posedge c0) x ##1 @(posedge c1) "
      "(y[*0:1] or x); endsequence";
  ExpectInstancesJudgedInEachPlace({
      {kTrailing, "me(clk0, clk1, a, b)", kEmptyWord},
      {kTrailing, "me(clk0, clk0, a, b)", ""},
      {kAlternative, "me(clk0, clk1, a, b)", kEmptyWord},
      {kAlternative, "me(clk0, clk0, a, b)", ""},
  });
}

}  // namespace
