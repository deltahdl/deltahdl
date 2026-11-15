#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InitialChecker(const std::string& items) {
  return "checker chk(input logic clk);\n"
         "  typedef struct packed { bit a; bit b; } pair_t;\n"
         "  typedef bit [1:0] two_t;\n"
         "  logic r;\n"
         "  bit [3:0] s;\n"
         "  bit [3:0] u [2];\n"
         "  bit c1, c2, c3, c4, e, g2, h, n;\n"
         "  int v;\n"
         "  pair_t m;\n"
         "  rand bit fr;\n" +
         items + "endchecker\n";
}

void ExpectInitialReport(const std::string& items, std::string_view var,
                         std::string_view at) {
  ElabFixture f;
  auto src = InitialChecker(items);
  ElaborateSrc(src, f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker variable '" + std::string(var) +
                                "' cannot be assigned in an initial procedure",
                            LineHolding(src, at), "17.7.1"));
}

void ExpectAccepted(const std::string& items) {
  ElabFixture f;
  ElaborateSrc(InitialChecker(items), f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableInInitial, AssignmentAfterAnEventControlIsReported) {
  ExpectInitialReport("  initial @(posedge clk) e = 1'b1;\n", "e", "e = 1'b1");
}

TEST(CheckerVariableInInitial, AssertionActionAfterAnEventControlIsReported) {
  ExpectInitialReport("  initial @(posedge clk) assert (r) g2 = 1'b1;\n", "g2",
                      "g2 = 1'b1");
}

TEST(CheckerVariableInInitial, BeginEndWithinAnActionBlockIsReported) {
  ExpectInitialReport("  initial assert (r) else begin h = 1'b1; end\n", "h",
                      "h = 1'b1");
}

TEST(CheckerVariableInInitial, ImmediateAssumeActionBlockIsReported) {
  ExpectInitialReport("  initial assume (r) h = 1'b1;\n", "h", "h = 1'b1");
}

TEST(CheckerVariableInInitial, ImmediateCoverActionBlockIsReported) {
  ExpectInitialReport("  initial cover (r) h = 1'b1;\n", "h", "h = 1'b1");
}

TEST(CheckerVariableInInitial, AssertPropertyActionBlockIsReported) {
  ExpectInitialReport(
      "  initial assert property (@(posedge clk) r) h = 1'b1;\n", "h",
      "h = 1'b1");
}

TEST(CheckerVariableInInitial, CoverPropertyActionBlockIsReported) {
  ExpectInitialReport("  initial cover property (@(posedge clk) r) h = 1'b1;\n",
                      "h", "h = 1'b1");
}

TEST(CheckerVariableInInitial, NonblockingWholeVariableIsReported) {
  ExpectInitialReport("  initial assert (r) n <= 1'b0;\n", "n", "n <= 1'b0");
}

TEST(CheckerVariableInInitial, CompoundOperatorsAreReported) {
  ExpectInitialReport("  initial assert (r) v += 1;\n", "v", "v += 1");
  ExpectInitialReport("  initial assert (r) v <<= 1;\n", "v", "v <<= 1");
}

TEST(CheckerVariableInInitial, FreeCheckerVariableIsReported) {
  ExpectInitialReport("  initial assert (r) fr <= 1'b1;\n", "fr", "fr <= 1'b1");
}

TEST(CheckerVariableInInitial, StructureMemberIsReported) {
  ExpectInitialReport("  initial assert (r) m.a = 1'b1;\n", "m", "m.a = 1'b1");
}

TEST(CheckerVariableInInitial, DISABLED_BitSelectIsReported) {
  ExpectInitialReport("  initial assert (r) s[0] = 1'b1;\n", "s",
                      "s[0] = 1'b1");
  ExpectInitialReport("  initial assert (r) s[0] <= 1'b1;\n", "s",
                      "s[0] <= 1'b1");
}

TEST(CheckerVariableInInitial, DISABLED_PartSelectsAreReported) {
  ExpectInitialReport("  initial assert (r) s[1:0] = 2'b01;\n", "s",
                      "s[1:0] = 2'b01");
  ExpectInitialReport("  initial assert (r) s[1+:2] = 2'b01;\n", "s",
                      "s[1+:2] = 2'b01");
}

TEST(CheckerVariableInInitial, DISABLED_UnpackedArrayElementIsReported) {
  ExpectInitialReport("  initial assert (r) u[0] = 4'h1;\n", "u",
                      "u[0] = 4'h1");
}

TEST(CheckerVariableInInitial, DISABLED_ConcatenationIsReported) {
  ExpectInitialReport("  initial assert (r) {c1, c2} = 2'b10;\n", "c1",
                      "{c1, c2} = 2'b10");
  ExpectInitialReport("  initial assert (r) {c1, c2} <= 2'b10;\n", "c2",
                      "{c1, c2} <= 2'b10");
}

TEST(CheckerVariableInInitial, DISABLED_StreamingConcatenationIsReported) {
  ExpectInitialReport("  initial assert (r) {>>{c1, c2}} = 2'b10;\n", "c1",
                      "{>>{c1, c2}}");
}

TEST(CheckerVariableInInitial, DISABLED_AssignmentPatternIsReported) {
  ExpectInitialReport("  initial assert (r) '{c3, c4} = two_t'(2'b10);\n", "c3",
                      "'{c3, c4}");
}

TEST(CheckerVariableInInitial, DISABLED_IncrementAndDecrementAreReported) {
  for (std::string_view stmt : {"v++;", "++v;", "v--;", "--v;"}) {
    SCOPED_TRACE(stmt);
    ExpectInitialReport("  initial assert (r) " + std::string(stmt) + "\n", "v",
                        stmt);
  }
}

TEST(CheckerVariableInInitial, DISABLED_VariableOfAnIfGenerateBlockIsReported) {
  ExpectInitialReport(
      "  if (1) begin : g\n"
      "    bit w;\n"
      "    initial assert (r) w = 1'b1;\n"
      "  end\n",
      "w", "w = 1'b1");
}

TEST(CheckerVariableInInitial,
     DISABLED_VariableOfACaseGenerateBlockIsReported) {
  ExpectInitialReport(
      "  case (1)\n"
      "    1: begin : g\n"
      "      bit w;\n"
      "      initial assert (r) w = 1'b1;\n"
      "    end\n"
      "  endcase\n",
      "w", "w = 1'b1");
}

TEST(CheckerVariableInInitial,
     DISABLED_VariableOfALoopGenerateBlockIsReported) {
  ExpectInitialReport(
      "  for (genvar k = 0; k < 1; k++) begin : g\n"
      "    bit w;\n"
      "    initial assert (r) w = 1'b1;\n"
      "  end\n",
      "w", "w = 1'b1");
}

TEST(CheckerVariableInInitial,
     DISABLED_CheckerBodyVariableAssignedFromAGenerateInitialIsReported) {
  ExpectInitialReport(
      "  if (1) begin : g\n"
      "    initial assert (r) h = 1'b1;\n"
      "  end\n",
      "h", "h = 1'b1");
}

TEST(CheckerVariableInInitial,
     DISABLED_GenerateVariableAssignedFromTheBodyByNameIsReported) {
  ExpectInitialReport(
      "  if (1) begin : g\n"
      "    bit w;\n"
      "  end\n"
      "  initial assert (r) g.w = 1'b1;\n",
      "w", "g.w = 1'b1");
}

TEST(CheckerVariableInInitial,
     DeclarationInitializerInAGenerateBlockIsAccepted) {
  ExpectAccepted(
      "  if (1) begin : g\n"
      "    bit w = 1'b0;\n"
      "  end\n");
}

TEST(CheckerVariableInInitial, ProcedureLocalVariableIsAccepted) {
  ExpectAccepted("  initial assert (r) begin bit q; q = 1'b1; end\n");
}

}  // namespace
