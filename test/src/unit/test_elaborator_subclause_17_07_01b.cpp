#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kAlwaysFfBlocking =
    "a blocking assignment cannot appear in an always_ff procedure of checker "
    "'chk'";

std::string CheckerHolding(const std::string& items) {
  return "checker chk(input logic clk, input logic d);\n"
         "  logic [3:0] q, r, f, g;\n"
         "  logic h;\n"
         "  logic [3:0] mem [4];\n" +
         items + "endchecker\n";
}

void ExpectReportAt(const std::string& src, std::string_view at,
                    std::string_view top) {
  ElabFixture f;
  ElaborateSrc(src, f, top);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kAlwaysFfBlocking,
                            LineHolding(src, at), "17.7.1"));
}

void ExpectAlwaysFfReport(const std::string& items, std::string_view at) {
  ExpectReportAt(CheckerHolding(items), at, "chk");
}

void ExpectAccepted(const std::string& items) {
  ElabFixture f;
  ElaborateSrc(CheckerHolding(items), f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerAlwaysFfBlockingForms, DISABLED_PostIncrementStatementIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) q++;\n", "q++");
}

TEST(CheckerAlwaysFfBlockingForms, DISABLED_PreIncrementStatementIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) ++q;\n", "++q");
}

TEST(CheckerAlwaysFfBlockingForms, DISABLED_PostDecrementStatementIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) q--;\n", "q--");
}

TEST(CheckerAlwaysFfBlockingForms, DISABLED_PreDecrementStatementIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) --q;\n", "--q");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_IncrementNestedInAnExpressionIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) f <= g++;\n", "g++");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_IncrementUnderIfElseAndBeginEndIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk) begin\n"
      "    if (d) q <= 4'd0;\n"
      "    else begin\n"
      "      r++;\n"
      "    end\n"
      "  end\n",
      "r++");
}

TEST(CheckerAlwaysFfBlockingForms, NonblockingIncrementFormIsAccepted) {
  ExpectAccepted("  always_ff @(posedge clk) q <= q + 4'd1;\n");
}

TEST(CheckerAlwaysFfBlockingForms, ForLoopStepWrittenAsIncrementIsAccepted) {
  ExpectAccepted(
      "  always_ff @(posedge clk)\n"
      "    for (int i = 0; i < 4; i++) mem[i] <= q;\n");
}

TEST(CheckerAlwaysFfBlockingForms, EveryCompoundAssignmentOperatorIsReported) {
  for (std::string_view op : {"+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
                              "<<=", ">>=", "<<<=", ">>>="}) {
    SCOPED_TRACE(op);
    std::string stmt = "q " + std::string(op) + " 4'd1;";
    ExpectAlwaysFfReport("  always_ff @(posedge clk) " + stmt + "\n", stmt);
  }
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_AssignmentOnANonblockingRightHandSideIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) h <= (r = d);\n", "(r = d)");
}

TEST(CheckerAlwaysFfBlockingForms, DISABLED_AssignmentInAConditionIsReported) {
  ExpectAlwaysFfReport("  always_ff @(posedge clk) if ((r = d)) h <= 1;\n",
                       "(r = d)");
}

TEST(CheckerAlwaysFfBlockingForms, ComparisonInAConditionIsAccepted) {
  ExpectAccepted("  always_ff @(posedge clk) if ((r == d)) h <= 1;\n");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentUnderIfElseIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk)\n"
      "    if (d) q <= 4'd1;\n"
      "    else r = 4'd2;\n",
      "r = 4'd2");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentUnderCaseIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk)\n"
      "    case (d)\n"
      "      1'b0: q <= 4'd1;\n"
      "      default: r = 4'd2;\n"
      "    endcase\n",
      "r = 4'd2");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentInAForBodyIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk)\n"
      "    for (int i = 0; i < 4; i = i + 1) mem[i] = q;\n",
      "mem[i] = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentInARepeatBodyIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk)\n"
      "    repeat (2) r = q;\n",
      "r = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentInAForeachBodyIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk)\n"
      "    foreach (mem[i]) r = q;\n",
      "r = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentInAWhileBodyIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk)\n"
      "    while (h) r = q;\n",
      "r = q");
}

TEST(CheckerAlwaysFfBlockingForms, NonblockingAssignmentsInLoopBodiesAccepted) {
  ExpectAccepted(
      "  always_ff @(posedge clk) begin\n"
      "    for (int i = 0; i < 4; i = i + 1) mem[i] <= q;\n"
      "    repeat (2) r <= q;\n"
      "    foreach (mem[j]) f <= q;\n"
      "  end\n");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentInANestedBeginEndIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk) begin\n"
      "    begin\n"
      "      begin\n"
      "        r = q;\n"
      "      end\n"
      "    end\n"
      "  end\n",
      "r = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_BlockingAssignmentToABlockLocalVariableIsReported) {
  ExpectAlwaysFfReport(
      "  always_ff @(posedge clk) begin\n"
      "    logic t;\n"
      "    t = d;\n"
      "    h <= t;\n"
      "  end\n",
      "t = d");
}

TEST(CheckerAlwaysFfBlockingForms,
     BlockingAssignmentInAnIfGenerateBlockIsReported) {
  ExpectAlwaysFfReport(
      "  if (1) begin : gb\n"
      "    always_ff @(posedge clk) r = q;\n"
      "  end\n",
      "r = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     DISABLED_IncrementInAnIfGenerateBlockIsReported) {
  ExpectAlwaysFfReport(
      "  if (1) begin : gb\n"
      "    always_ff @(posedge clk) r++;\n"
      "  end\n",
      "r++");
}

TEST(CheckerAlwaysFfBlockingForms,
     BlockingAssignmentInACaseGenerateBlockIsReported) {
  ExpectAlwaysFfReport(
      "  case (1)\n"
      "    1: begin : gb\n"
      "      always_ff @(posedge clk) r = q;\n"
      "    end\n"
      "  endcase\n",
      "r = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     BlockingAssignmentInAForGenerateBlockIsReported) {
  ExpectAlwaysFfReport(
      "  for (genvar k = 0; k < 2; k++) begin : gb\n"
      "    always_ff @(posedge clk) mem[k] = q;\n"
      "  end\n",
      "mem[k] = q");
}

TEST(CheckerAlwaysFfBlockingForms,
     NonblockingAssignmentsInGenerateBlocksAreAccepted) {
  ExpectAccepted(
      "  if (1) begin : g1\n"
      "    always_ff @(posedge clk) r <= q;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : g2\n"
      "      always_ff @(posedge clk) f <= q;\n"
      "    end\n"
      "  endcase\n"
      "  for (genvar k = 0; k < 2; k++) begin : g3\n"
      "    always_ff @(posedge clk) mem[k] <= q;\n"
      "  end\n");
}

constexpr std::string_view kChkWithBlockingAlwaysFf =
    "checker chk(input logic clk, input logic d);\n"
    "  logic q;\n"
    "  always_ff @(posedge clk) q = d;\n"
    "endchecker\n";

TEST(CheckerAlwaysFfBlockingForms, CheckerDeclaredInAPackageIsReported) {
  ExpectReportAt("package p;\n" + std::string(kChkWithBlockingAlwaysFf) +
                     "endpackage\n"
                     "module top;\n"
                     "  import p::*;\n"
                     "  logic clk, d;\n"
                     "  chk k(clk, d);\n"
                     "endmodule\n",
                 "q = d", "top");
}

TEST(CheckerAlwaysFfBlockingForms,
     CheckerDeclaredInTheCompilationUnitIsReported) {
  ExpectReportAt(std::string(kChkWithBlockingAlwaysFf) +
                     "module top;\n"
                     "  logic clk, d;\n"
                     "  chk k(clk, d);\n"
                     "endmodule\n",
                 "q = d", "top");
}

TEST(CheckerAlwaysFfBlockingForms, CheckerNestedInAnotherCheckerIsReported) {
  ExpectReportAt("checker outer(input logic clk, input logic d);\n" +
                     std::string(kChkWithBlockingAlwaysFf) +
                     "  chk k(clk, d);\n"
                     "endchecker\n"
                     "module top;\n"
                     "  logic clk, d;\n"
                     "  outer o(clk, d);\n"
                     "endmodule\n",
                 "q = d", "top");
}

TEST(CheckerAlwaysFfBlockingForms,
     NonblockingFormInAPackageAndANestedCheckerIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  checker pc(input logic clk, input logic d);\n"
      "    logic q;\n"
      "    always_ff @(posedge clk) q <= d;\n"
      "  endchecker\n"
      "endpackage\n"
      "checker outer(input logic clk, input logic d);\n"
      "  checker inner(input logic clk, input logic d);\n"
      "    logic q;\n"
      "    always_ff @(posedge clk) q <= d;\n"
      "  endchecker\n"
      "  inner k(clk, d);\n"
      "endchecker\n"
      "module top;\n"
      "  import p::*;\n"
      "  logic clk, d;\n"
      "  pc c(clk, d);\n"
      "  outer o(clk, d);\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
