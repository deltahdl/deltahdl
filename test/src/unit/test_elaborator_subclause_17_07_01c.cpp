#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string FreeChecker(const std::string& items) {
  return "checker chk(input logic clk, input logic en, input logic a);\n"
         "  typedef struct packed { bit p; bit q; } pair_t;\n"
         "  rand bit b, c;\n"
         "  rand bit [3:0] x;\n"
         "  rand bit u [2];\n"
         "  rand pair_t s;\n"
         "  bit o, o2;\n"
         "  bit [3:0] ov;\n"
         "  bit ou [2];\n"
         "  pair_t os;\n"
         "  int i;\n" +
         items + "endchecker\n";
}

std::string BlockingMessage(std::string_view var) {
  return "a blocking assignment cannot target free checker variable '" +
         std::string(var) + "'";
}

std::string ContinuousMessage(std::string_view var) {
  return "a continuous assignment cannot target free checker variable '" +
         std::string(var) + "'";
}

void ExpectReport(const std::string& items, const std::string& message,
                  std::string_view at) {
  ElabFixture f;
  auto src = FreeChecker(items);
  ElaborateSrc(src, f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, LineHolding(src, at),
                            "17.7.1"));
}

void ExpectBlockingReport(const std::string& items, std::string_view var,
                          std::string_view at) {
  ExpectReport(items, BlockingMessage(var), at);
}

void ExpectContinuousReport(const std::string& items, std::string_view var,
                            std::string_view at) {
  ExpectReport(items, ContinuousMessage(var), at);
}

void ExpectAccepted(const std::string& items) {
  ElabFixture f;
  ElaborateSrc(FreeChecker(items), f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(FreeCheckerVariableAssignment, BlockingWriteInACaseItemIsReported) {
  ExpectBlockingReport(
      "  always_comb\n"
      "    case (a)\n"
      "      1'b1: b = en;\n"
      "      default: o = en;\n"
      "    endcase\n",
      "b", "b = en");
}

TEST(FreeCheckerVariableAssignment, BlockingWriteInAnElseBranchIsReported) {
  ExpectBlockingReport(
      "  always_comb\n"
      "    if (en) o = a;\n"
      "    else b = a;\n",
      "b", "b = a");
}

TEST(FreeCheckerVariableAssignment, BlockingWriteInAForBodyIsReported) {
  ExpectBlockingReport(
      "  always_comb\n"
      "    for (int k = 0; k < 2; k = k + 1) b = a;\n",
      "b", "b = a");
}

TEST(FreeCheckerVariableAssignment, BlockingWriteInARepeatBodyIsReported) {
  ExpectBlockingReport("  always_comb repeat (2) b = a;\n", "b", "b = a");
}

TEST(FreeCheckerVariableAssignment, BlockingWriteInAWhileBodyIsReported) {
  ExpectBlockingReport("  always_comb while (en) b = a;\n", "b", "b = a");
}

TEST(FreeCheckerVariableAssignment, BlockingWriteInAlwaysFfIsReported) {
  ExpectBlockingReport("  always_ff @(posedge clk) b = a;\n", "b", "b = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_BlockingWriteToABitSelectIsReported) {
  ExpectBlockingReport("  always_comb x[0] = a;\n", "x", "x[0] = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_ContinuousWriteToABitSelectIsReported) {
  ExpectContinuousReport("  assign x[1] = a;\n", "x", "x[1] = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_BlockingWriteToAPartSelectIsReported) {
  ExpectBlockingReport("  always_comb x[3:2] = 2'd1;\n", "x", "x[3:2]");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_ContinuousWriteToAPartSelectIsReported) {
  ExpectContinuousReport("  assign x[3:2] = 2'd1;\n", "x", "x[3:2]");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_BlockingWriteToAnUnpackedElementIsReported) {
  ExpectBlockingReport("  always_comb u[1] = a;\n", "u", "u[1] = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_ContinuousWriteToAnUnpackedElementIsReported) {
  ExpectContinuousReport("  assign u[1] = a;\n", "u", "u[1] = a");
}

TEST(FreeCheckerVariableAssignment, BlockingWriteToAMemberIsReported) {
  ExpectBlockingReport("  always_comb s.p = a;\n", "s", "s.p = a");
}

TEST(FreeCheckerVariableAssignment, ContinuousWriteToAMemberIsReported) {
  ExpectContinuousReport("  assign s.p = a;\n", "s", "s.p = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_BlockingWriteThroughAConcatenationIsReported) {
  ElabFixture f;
  auto src = FreeChecker("  always_comb {b, c} = {a, a};\n");
  ElaborateSrc(src, f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BlockingMessage("b"),
                            LineHolding(src, "{b, c}"), "17.7.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BlockingMessage("c"),
                            LineHolding(src, "{b, c}"), "17.7.1"));
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_ContinuousWriteThroughAConcatenationIsReported) {
  ElabFixture f;
  auto src = FreeChecker("  assign {b, c} = {a, a};\n");
  ElaborateSrc(src, f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), ContinuousMessage("b"),
                            LineHolding(src, "{b, c}"), "17.7.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), ContinuousMessage("c"),
                            LineHolding(src, "{b, c}"), "17.7.1"));
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_BlockingWriteThroughAMixedConcatenationIsReported) {
  ExpectBlockingReport("  always_comb {o, b} = {a, a};\n", "b", "{o, b}");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_ContinuousWriteThroughAMixedConcatenationIsReported) {
  ExpectContinuousReport("  assign {o, b} = {a, a};\n", "b", "{o, b}");
}

TEST(FreeCheckerVariableAssignment, DISABLED_IncrementAndDecrementAreReported) {
  for (std::string_view stmt : {"x++;", "++x;", "x--;", "--x;"}) {
    SCOPED_TRACE(stmt);
    ExpectBlockingReport("  always_comb " + std::string(stmt) + "\n", "x",
                         stmt);
  }
}

TEST(FreeCheckerVariableAssignment, EveryCompoundAssignmentOperatorIsReported) {
  for (std::string_view op : {"+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
                              "<<=", ">>=", "<<<=", ">>>="}) {
    SCOPED_TRACE(op);
    std::string stmt = "x " + std::string(op) + " 4'd1;";
    ExpectBlockingReport("  always_comb " + stmt + "\n", "x", stmt);
  }
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_WritesToAFreeVariableOfAnIfGenerateBlockAreReported) {
  std::string items =
      "  if (1) begin : g\n"
      "    rand bit p, q;\n"
      "    assign p = a;\n"
      "    always_comb q = a;\n"
      "  end\n";
  ExpectContinuousReport(items, "p", "p = a");
  ExpectBlockingReport(items, "q", "q = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_WritesToAFreeVariableOfACaseGenerateBlockAreReported) {
  std::string items =
      "  case (1)\n"
      "    1: begin : g\n"
      "      rand bit p, q;\n"
      "      assign p = a;\n"
      "      always_comb q = a;\n"
      "    end\n"
      "  endcase\n";
  ExpectContinuousReport(items, "p", "p = a");
  ExpectBlockingReport(items, "q", "q = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_WritesToAFreeVariableOfAForGenerateBlockAreReported) {
  std::string items =
      "  for (genvar k = 0; k < 1; k++) begin : g\n"
      "    rand bit p, q;\n"
      "    assign p = a;\n"
      "    always_comb q = a;\n"
      "  end\n";
  ExpectContinuousReport(items, "p", "p = a");
  ExpectBlockingReport(items, "q", "q = a");
}

TEST(FreeCheckerVariableAssignment,
     DISABLED_WritesFromAGenerateBlockToATopFreeVariableAreReported) {
  std::string items =
      "  if (1) begin : g\n"
      "    assign b = a;\n"
      "    always_comb c = a;\n"
      "  end\n";
  ExpectContinuousReport(items, "b", "b = a");
  ExpectBlockingReport(items, "c", "c = a");
}

TEST(FreeCheckerVariableAssignment,
     BlockingWriteToAConstFreeVariableIsReported) {
  ElabFixture f;
  auto src = FreeChecker(
      "  rand const bit k;\n"
      "  always_comb k = a;\n");
  ElaborateSrc(src, f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BlockingMessage("k"),
                            LineHolding(src, "k = a"), "17.7.1"));
}

TEST(FreeCheckerVariableAssignment,
     ContinuousWriteToAnOrdinaryCheckerVariableIsAccepted) {
  ExpectAccepted("  assign o = a;\n");
}

TEST(FreeCheckerVariableAssignment,
     PartialAndConcatenatedWritesToOrdinaryVariablesAreAccepted) {
  ExpectAccepted(
      "  always_comb ov[0] = a;\n"
      "  assign ov[3:2] = 2'd1;\n"
      "  always_comb os.p = a;\n"
      "  assign os.q = a;\n"
      "  always_comb ou[0] = a;\n"
      "  assign ou[1] = a;\n"
      "  always_comb {o, o2} = {a, a};\n");
}

TEST(FreeCheckerVariableAssignment,
     NonblockingPartialAndConcatenatedWritesInAlwaysFfAreAccepted) {
  ExpectAccepted(
      "  always_ff @(posedge clk) begin\n"
      "    x[0] <= a;\n"
      "    x[3:2] <= 2'd1;\n"
      "    s.p <= a;\n"
      "    u[1] <= a;\n"
      "    {b, c} <= {a, a};\n"
      "  end\n");
}

TEST(FreeCheckerVariableAssignment,
     NonblockingWritesInAlwaysCombAndAlwaysLatchAreAccepted) {
  ExpectAccepted(
      "  always_comb b <= a;\n"
      "  always_latch if (en) c <= a;\n");
}

TEST(FreeCheckerVariableAssignment,
     NonblockingWritesInAndFromAGenerateBlockAreAccepted) {
  ExpectAccepted(
      "  if (1) begin : g\n"
      "    rand bit p;\n"
      "    always_ff @(posedge clk) p <= a;\n"
      "    always_ff @(posedge clk) b <= a;\n"
      "  end\n");
}

}  // namespace
