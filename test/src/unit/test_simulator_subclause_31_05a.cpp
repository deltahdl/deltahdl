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

TEST(EdgeControlSpecifierEvaluation, SetupEdge01IgnoresAZeroToXTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[01] clk, 23);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #101 d = 1'b1;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

TEST(EdgeControlSpecifierEvaluation, SetupEdge01AnswersToAZeroToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[01] clk, 23);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #101 d = 1'b1;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01] clk"), "31.3.1"));
}

TEST(EdgeControlSpecifierEvaluation, PosedgeListAnswersToAZeroToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[01, 0x, x1] clk, 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #113 d = 1'b1;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01, 0x, x1] clk"), "31.3.1"));
}

TEST(EdgeControlSpecifierEvaluation, PosedgeListAnswersToAZeroToXTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[01, 0x, x1] clk, 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #127 d = 1'b1;\n"
      "    #9 clk = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01, 0x, x1] clk"), "31.3.1"));
}

TEST(EdgeControlSpecifierEvaluation, PosedgeListAnswersToAnXToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[01, 0x, x1] clk, 31);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'bx;\n"
      "    #149 d = 1'b1;\n"
      "    #11 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[01, 0x, x1] clk"), "31.3.1"));
}

TEST(EdgeControlSpecifierEvaluation, SetupEdge1xIgnoresAOneToZeroTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[1x] clk, 43);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b1;\n"
      "    #167 d = 1'b1;\n"
      "    #13 clk = 1'b0;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

TEST(EdgeControlSpecifierEvaluation, SetupEdgeZ1AnswersToAnXToOneTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, edge[z1] clk, 59);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'bx;\n"
      "    #181 d = 1'b1;\n"
      "    #17 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setup violation: data signal",
      LineHolding(kDesign, "$setup(d, edge[z1] clk"), "31.3.1"));
}

TEST(EdgeControlSpecifierEvaluation, WidthEdge01ClosesOnAOneToZeroTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $width(edge[01] clk, 71, 0);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #191 clk = 1'b1;\n"
      "    #3 clk = 1'b0;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "$width violation: signal",
                              LineHolding(kDesign, "$width(edge[01] clk"),
                              "31.4.4"));
}

TEST(EdgeControlSpecifierEvaluation, WidthEdge01IgnoresAOneToXTransition) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $width(edge[01] clk, 71, 0);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #211 clk = 1'b1;\n"
      "    #4 clk = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

}  // namespace
