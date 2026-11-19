#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr std::size_t kNotRun = 1000;

std::size_t ReportsOf(const std::string& decls, const std::string& check,
                      const std::string& stimulus, const std::string& report) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  " +
      decls +
      "\n"
      "  specify\n"
      "    " +
      check +
      "\n"
      "  endspecify\n"
      "  initial begin\n"
      "    " +
      stimulus +
      "\n"
      "  end\n"
      "endmodule\n";
  auto* rtl = ElaborateSrc(kDesign, f);
  if (rtl == nullptr || f.has_errors) return kNotRun;
  LowerAndRun(rtl, f);
  std::size_t count = 0;
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.message.rfind(report, 0) == 0) ++count;
  }
  return count;
}

constexpr const char* kScalarNet = "logic e; wire en = e;";
constexpr const char* kSetupReport = "$setup violation: data signal";

std::string SetupStimulus(const std::string& e) {
  return "d = 1'b0; clk = 1'b0; e = " + e + "; #13 d = 1'b1; #6 clk = 1'b1;";
}

std::size_t SetupReports(const std::string& condition, const std::string& e) {
  return ReportsOf(kScalarNet,
                   "$setup(d, posedge clk &&& " + condition + ", 29);",
                   SetupStimulus(e), kSetupReport);
}

struct ConditionRun {
  std::string condition;
  std::string e;
  std::size_t reports;
};

void ExpectSetupReports(const std::vector<ConditionRun>& runs) {
  for (const ConditionRun& run : runs) {
    EXPECT_EQ(SetupReports(run.condition, run.e), run.reports)
        << run.condition << " with e = " << run.e;
  }
}

TEST(ConditionedTimingCheckRun, NegatedConditionAtOneSuppressesTheCheck) {
  ExpectSetupReports({{"~en", "1'b1", 0}, {"~en", "1'b0", 1}});
}

TEST(ConditionedTimingCheckRun, ComparisonFormsEnableOrSuppressTheCheck) {
  ExpectSetupReports({
      {"en == 1'b1", "1'b1", 1},
      {"en == 1'b1", "1'b0", 0},
      {"en == 1'b0", "1'b0", 1},
      {"en == 1'b0", "1'b1", 0},
      {"en === 1'b1", "1'b1", 1},
      {"en === 1'b1", "1'b0", 0},
      {"en === 1'b0", "1'b0", 1},
      {"en === 1'b0", "1'b1", 0},
      {"en != 1'b0", "1'b1", 1},
      {"en != 1'b0", "1'b0", 0},
      {"en != 1'b1", "1'b0", 1},
      {"en != 1'b1", "1'b1", 0},
      {"en !== 1'b0", "1'b1", 1},
      {"en !== 1'b0", "1'b0", 0},
      {"en !== 1'b1", "1'b0", 1},
      {"en !== 1'b1", "1'b1", 0},
  });
}

TEST(ConditionedTimingCheckRun, DeterministicFormsAtXSuppressTheCheck) {
  ExpectSetupReports({
      {"en", "1'bx", 0},
      {"~en", "1'bx", 0},
      {"en === 1'b1", "1'bx", 0},
      {"en === 1'b0", "1'bx", 0},
      {"en !== 1'b0", "1'bx", 0},
      {"en !== 1'b1", "1'bx", 0},
  });
}

TEST(ConditionedTimingCheckRun, NondeterministicFormsAtXEnableTheCheck) {
  ExpectSetupReports({
      {"en == 1'b1", "1'bx", 1},
      {"en == 1'b0", "1'bx", 1},
      {"en != 1'b0", "1'bx", 1},
      {"en != 1'b1", "1'bx", 1},
  });
}

TEST(ConditionedTimingCheckRun, ContinuouslyAssignedNetGatesTheCheck) {
  ExpectSetupReports({{"en", "1'b0", 0}, {"en", "1'b1", 1}});
}

std::size_t VectorSetupReports(const std::string& condition,
                               const std::string& e) {
  return ReportsOf("logic [1:0] e; wire [1:0] en = e;",
                   "$setup(d, posedge clk &&& " + condition + ", 29);",
                   SetupStimulus(e), kSetupReport);
}

TEST(ConditionedTimingCheckRun, VectorNetGatesByItsLeastSignificantBit) {
  EXPECT_EQ(VectorSetupReports("en", "2'b10"), 0u);
  EXPECT_EQ(VectorSetupReports("en", "2'b01"), 1u);
}

TEST(ConditionedTimingCheckRun, VectorNetComparisonUsesItsLeastSignificantBit) {
  EXPECT_EQ(VectorSetupReports("en == 1'b1", "2'b11"), 1u);
  EXPECT_EQ(VectorSetupReports("en == 1'b1", "2'b10"), 0u);
}

TEST(ConditionedTimingCheckRun,
     MultibitExpressionGatesByItsLeastSignificantBit) {
  EXPECT_EQ(VectorSetupReports("(en & 2'b10)", "2'b11"), 0u);
  EXPECT_EQ(VectorSetupReports("(en & 2'b11)", "2'b01"), 1u);
}

TEST(ConditionedTimingCheckRun, TrueDataConditionLetsAHoldReport) {
  const std::string kStimulus =
      "d = 1'b0; clk = 1'b0; e = %; #26 clk = 1'b1; #5 d = 1'b1;";
  for (const auto& [e, reports] :
       std::vector<std::pair<std::string, std::size_t>>{{"1'b1", 1},
                                                        {"1'b0", 0}}) {
    std::string stimulus = kStimulus;
    stimulus.replace(stimulus.find('%'), 1, e);
    EXPECT_EQ(ReportsOf(kScalarNet, "$hold(posedge clk, d &&& en, 67);",
                        stimulus, "$hold violation: data signal"),
              reports)
        << e;
  }
}

struct GatedCheck {
  std::string check;
  std::string stimulus;
  std::string report;
};

void ExpectGatedByTheCondition(const GatedCheck& gated) {
  for (const auto& [e, enabled] : std::vector<std::pair<std::string, bool>>{
           {"1'b1", true}, {"1'b0", false}}) {
    const std::size_t kReports = ReportsOf(
        kScalarNet, gated.check,
        "d = 1'b0; clk = 1'b0; e = " + e + "; " + gated.stimulus, gated.report);
    ASSERT_NE(kReports, kNotRun) << gated.check;
    if (enabled) {
      EXPECT_GE(kReports, 1u) << gated.check;
    } else {
      EXPECT_EQ(kReports, 0u) << gated.check;
    }
  }
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheWidthCheck) {
  ExpectGatedByTheCondition({"$width(posedge clk &&& en, 20);",
                             "#10 clk = 1'b1; #5 clk = 1'b0;",
                             "$width violation: signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesThePeriodCheck) {
  ExpectGatedByTheCondition({"$period(posedge clk &&& en, 20);",
                             "#10 clk = 1'b1; #5 clk = 1'b0; #5 clk = 1'b1;",
                             "$period violation: signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheRecoveryCheck) {
  ExpectGatedByTheCondition({"$recovery(posedge clk &&& en, d, 20);",
                             "#10 clk = 1'b1; #5 d = 1'b1;",
                             "$recovery violation: data signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheRemovalCheck) {
  ExpectGatedByTheCondition({"$removal(posedge clk &&& en, d, 20);",
                             "#10 d = 1'b1; #5 clk = 1'b1;",
                             "$removal violation: data signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheSetupholdCheck) {
  ExpectGatedByTheCondition({"$setuphold(posedge clk &&& en, d, 10, 10);",
                             "#10 clk = 1'b1; #5 d = 1'b1;",
                             "$setuphold violation: data signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheRecremCheck) {
  ExpectGatedByTheCondition({"$recrem(posedge clk &&& en, d, 10, 10);",
                             "#10 clk = 1'b1; #5 d = 1'b1;",
                             "$recrem violation: data signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheSkewCheck) {
  ExpectGatedByTheCondition({"$skew(posedge clk &&& en, d, 3);",
                             "#10 clk = 1'b1; #5 d = 1'b1;",
                             "$skew violation: data signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheTimeskewCheck) {
  ExpectGatedByTheCondition({"$timeskew(posedge clk &&& en, posedge d, 3);",
                             "#10 clk = 1'b1; #5 d = 1'b1;",
                             "$timeskew violation: data signal"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheFullskewCheck) {
  ExpectGatedByTheCondition(
      {"$fullskew(posedge clk &&& en, posedge d, 3, 3, , 1, 0);",
       "#10 clk = 1'b1; #5 d = 1'b1;", "$fullskew violation: signals"});
}

TEST(ConditionedTimingCheckRun, ConditionGatesTheNochangeCheck) {
  ExpectGatedByTheCondition({"$nochange(posedge clk &&& en, d, 0, 0);",
                             "#10 clk = 1'b1; #5 d = 1'b1; #5 clk = 1'b0;",
                             "$nochange violation: data signal"});
}

std::string TwoViolatingEdges(const std::string& first,
                              const std::string& second) {
  return "d = 1'b0; clk = 1'b0; e = " + first +
         "; #13 d = 1'b1; #6 clk = 1'b1; #1 clk = 1'b0; e = " + second +
         "; #3 d = 1'b0; #6 clk = 1'b1;";
}

TEST(ConditionedTimingCheckRun, ConditionIsSampledAtEachEvent) {
  const std::string kCheck = "$setup(d, posedge clk &&& en, 29);";
  EXPECT_EQ(ReportsOf(kScalarNet, kCheck, TwoViolatingEdges("1'b0", "1'b1"),
                      kSetupReport),
            1u);
  EXPECT_EQ(ReportsOf(kScalarNet, kCheck, TwoViolatingEdges("1'b1", "1'b0"),
                      kSetupReport),
            1u);
}

TEST(ConditionedTimingCheckRun, UnconditionedEventIsCheckedAtEveryEdge) {
  EXPECT_EQ(ReportsOf(kScalarNet, "$setup(d, posedge clk, 29);",
                      TwoViolatingEdges("1'b0", "1'b0"), kSetupReport),
            2u);
}

}  // namespace
