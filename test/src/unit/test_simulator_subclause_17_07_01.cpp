#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string CheckerOverCount(const std::string& body) {
  return "checker chk(int b, logic clk);\n" + body +
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  int b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) b = b + 1;\n"
         "  chk c(b, clk);\n"
         "  initial #42 $finish;\n"
         "endmodule\n";
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST(CheckerVariableAssignmentRun, NonblockingInAlwaysCombFollowsItsSource) {
  SimFixture f;
  auto* n = RunAndFindVar(CheckerOverCount("  int n;\n"
                                           "  always_comb n <= b;\n"),
                          f, "c.n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 4u);
}

TEST(CheckerVariableAssignmentRun,
     NonblockingInAlwaysLatchFollowsWhileEnabledAndHolds) {
  SimFixture f;
  auto* l =
      RunAndFindVar(CheckerOverCount("  int l;\n"
                                     "  always_latch if (b < 3) l <= b;\n"),
                    f, "c.l");
  ASSERT_NE(l, nullptr);
  EXPECT_EQ(l->value.ToUint64(), 2u);
}

TEST(CheckerVariableAssignmentRun, EveryAllowedFormRunsInAGenerateBlock) {
  SimFixture f;
  auto* design =
      ElaborateSrc(CheckerOverCount("  if (1) begin : g\n"
                                    "    int x1, x2, x3, x4, x5, x6;\n"
                                    "    assign x1 = b;\n"
                                    "    always_comb x2 = b;\n"
                                    "    always_latch if (b < 3) x3 = b;\n"
                                    "    always_comb x4 <= b;\n"
                                    "    always_latch if (b < 3) x5 <= b;\n"
                                    "    always_ff @(posedge clk) x6 <= b;\n"
                                    "  end\n"),
                   f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(ValueOf(f, "c.g.x1"), 4u);
  EXPECT_EQ(ValueOf(f, "c.g.x2"), 4u);
  EXPECT_EQ(ValueOf(f, "c.g.x3"), 2u);
  EXPECT_EQ(ValueOf(f, "c.g.x4"), 4u);
  EXPECT_EQ(ValueOf(f, "c.g.x5"), 2u);
  EXPECT_EQ(ValueOf(f, "c.g.x6"), 3u);
}

constexpr std::string_view kEndPointStimulus =
    "  logic clk = 0, a = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  initial begin #2 a = 1; #30 a = 0; #20 $finish; end\n";

std::string FirstRiseRecorder(std::string_view watched) {
  return "  int first = 0;\n"
         "  always_ff @(posedge " +
         std::string(watched) + ") if (first == 0) first <= $time;\n";
}

std::string EndPointChecker(const std::string& items) {
  return "checker chk(logic a, logic clk);\n"
         "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
         "  bit en = 1'b1, z = 1'b0;\n" +
         items + FirstRiseRecorder("cv") +
         "endchecker\n"
         "module top;\n" +
         std::string(kEndPointStimulus) +
         "  chk c(a, clk);\n"
         "endmodule\n";
}

void ExpectFirstRiseAtTheEndPoint(const std::string& src,
                                  std::string_view first = "c.first") {
  SimFixture f;
  auto* var = RunAndFindVar(src, f, first);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(CheckerTriggeredAssignment, AlwaysFfNonblockingTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  always_ff @(posedge clk) cv <= s.triggered;\n"));
}

TEST(CheckerTriggeredAssignment,
     DISABLED_ContinuousAssignmentTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  assign cv = s.triggered;\n"));
}

TEST(CheckerTriggeredAssignment, DISABLED_AlwaysCombBlockingTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  always_comb cv = s.triggered;\n"));
}

TEST(CheckerTriggeredAssignment,
     DISABLED_AlwaysCombNonblockingTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  always_comb cv <= s.triggered;\n"));
}

TEST(CheckerTriggeredAssignment, DISABLED_AlwaysLatchBlockingTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  always_latch if (en) cv = s.triggered;\n"));
}

TEST(CheckerTriggeredAssignment,
     DISABLED_AlwaysLatchNonblockingTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  always_latch if (en) cv <= s.triggered;\n"));
}

TEST(CheckerTriggeredAssignment, ConjunctionInAlwaysFfTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  always_ff @(posedge clk) cv <= s.triggered && a;\n"));
}

TEST(CheckerTriggeredAssignment,
     DISABLED_DisjunctionInAContinuousAssignTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  bit cv;\n"
                      "  assign cv = s.triggered || z;\n"));
}

TEST(CheckerTriggeredAssignment,
     SequenceInstanceWithArgumentsTakesItsEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  sequence s2(x); @(posedge clk) x ##1 x; endsequence\n"
                      "  bit cv;\n"
                      "  always_ff @(posedge clk) cv <= s2(a).triggered;\n"));
}

std::string SequenceFormalChecker(std::string_view module_items,
                                  std::string_view actual) {
  return "checker chk(sequence sf, logic clk);\n"
         "  bit cv;\n"
         "  always_ff @(posedge clk) cv <= sf.triggered;\n" +
         FirstRiseRecorder("cv") +
         "endchecker\n"
         "module top;\n" +
         std::string(kEndPointStimulus) + std::string(module_items) +
         "  chk c(" + std::string(actual) +
         ", clk);\n"
         "endmodule\n";
}

TEST(CheckerTriggeredAssignment,
     SequenceFormalBoundToAModuleSequenceTakesItsEndPoint) {
  ExpectFirstRiseAtTheEndPoint(SequenceFormalChecker(
      "  sequence ms; @(posedge clk) a ##1 a; endsequence\n", "ms"));
}

TEST(CheckerTriggeredAssignment,
     SequenceFormalBoundToASequenceExpressionTakesItsEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      SequenceFormalChecker("", "@(posedge clk) a ##1 a"));
}

TEST(CheckerTriggeredAssignment, DISABLED_PackageSequenceTakesItsEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      "package p;\n"
      "  sequence ps(x, ck); @(posedge ck) x ##1 x; endsequence\n"
      "endpackage\n" +
      EndPointChecker(
          "  bit cv;\n"
          "  always_ff @(posedge clk) cv <= p::ps(a, clk).triggered;\n"));
}

TEST(CheckerTriggeredAssignment, FreeVariableNonblockingTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      EndPointChecker("  rand bit cv = 1'b0;\n"
                      "  always_ff @(posedge clk) cv <= s.triggered;\n"));
}

std::string GenerateEndPointChecker(const std::string& assignment) {
  return EndPointChecker(
      "  bit cv;\n"
      "  if (1) begin : g\n"
      "    bit gv;\n" +
      assignment + FirstRiseRecorder("gv") + "  end\n");
}

TEST(CheckerTriggeredAssignment,
     DISABLED_ContinuousAssignmentInAGenerateBlockTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      GenerateEndPointChecker("    assign gv = s.triggered;\n"), "c.g.first");
}

TEST(CheckerTriggeredAssignment,
     DISABLED_AlwaysCombInAGenerateBlockTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      GenerateEndPointChecker("    always_comb gv = s.triggered;\n"),
      "c.g.first");
}

TEST(CheckerTriggeredAssignment, AlwaysFfInAGenerateBlockTakesTheEndPoint) {
  ExpectFirstRiseAtTheEndPoint(
      GenerateEndPointChecker(
          "    always_ff @(posedge clk) gv <= s.triggered;\n"),
      "c.g.first");
}

}  // namespace
