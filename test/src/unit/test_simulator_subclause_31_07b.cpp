#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(ConditionedTimingCheckEvaluation, SetupWithFalseConditionReportsNothing) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& en, 29);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b0;\n"
      "    #13 d = 1'b1;\n"
      "    #6 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

TEST(ConditionedTimingCheckEvaluation, SetupWithTrueConditionIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& en, 29);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b1;\n"
      "    #13 d = 1'b1;\n"
      "    #6 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& en"), "31.3.1"));
}

TEST(ConditionedTimingCheckEvaluation, PlainConditionAtXReportsNothing) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& en, 37);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'bx;\n"
      "    #22 d = 1'b1;\n"
      "    #8 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

TEST(ConditionedTimingCheckEvaluation, EqualityConditionAtXIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& (en == 1'b1), 41);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'bx;\n"
      "    #44 d = 1'b1;\n"
      "    #11 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& (en == 1'b1)"),
      "31.3.1"));
}

TEST(ConditionedTimingCheckEvaluation, NegatedConditionAtZeroIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& ~en, 53);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b0;\n"
      "    #61 d = 1'b1;\n"
      "    #15 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& ~en"), "31.3.1"));
}

TEST(ConditionedTimingCheckEvaluation,
     HoldWithFalseDataConditionReportsNothing) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en;\n"
      "  specify\n"
      "    $hold(posedge clk, d &&& en, 67);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b0;\n"
      "    #83 clk = 1'b1;\n"
      "    #9 d = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$hold violation: data signal"), nullptr);
}

TEST(ConditionedTimingCheckEvaluation,
     ComparisonWithASignalIsEvaluatedAsAWhole) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic en, sel;\n"
      "  specify\n"
      "    $setup(d, posedge clk &&& (en == sel), 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 1'b1;\n"
      "    sel = 1'b1;\n"
      "    #17 d = 1'b1;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, posedge clk &&& (en == sel)"), "31.3.1"));
}

TEST(ConditionedTimingCheckEvaluation,
     ComparisonWithAWideLiteralIsEvaluatedAsAWhole) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic [1:0] en;\n"
      "  specify\n"
      "    $hold(posedge clk, d &&& (en == 2'b10), 43);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    en = 2'b00;\n"
      "    #26 clk = 1'b1;\n"
      "    #5 d = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$hold violation: data signal"), nullptr);
}

}  // namespace
