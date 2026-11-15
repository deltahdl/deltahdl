#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InferenceDesign(const std::string& items) {
  return "module m;\n"
         "  logic clk_a, clk_d, clk_e, a, b, c;\n"
         "  sequence e4; b ##1 c; endsequence\n"
         "  sequence g4; @(posedge clk_a) b ##1 c; endsequence\n"
         "  sequence h4; @(posedge clk_e) b ##1 c; endsequence\n"
         "  sequence f4(event ck = $inferred_clock); @(ck) b ##1 c; "
         "endsequence\n" +
         items + "endmodule\n";
}

size_t ErrorCount(const std::vector<Diagnostic>& diags) {
  size_t n = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError) ++n;
  }
  return n;
}

size_t CountHolding(const std::vector<Diagnostic>& diags,
                    const std::string& text) {
  size_t n = 0;
  for (const auto& diag : diags) {
    if (diag.message.find(text) != std::string::npos) ++n;
  }
  return n;
}

void ExpectAccepted(const std::string& items) {
  ElabFixture f;
  std::string src = InferenceDesign(items);
  ElaborateSrc(src, f);
  EXPECT_EQ(ErrorCount(f.diag.Diagnostics()), 0u) << src;
}

const char* const kNoClockReport =
    "has no explicit clocking event, and no clock can be inferred where it "
    "is used";

const char* const kClockExpressionReport =
    "triggered of the sequence 'e4', which has no explicit clocking event, "
    "may not stand in a clock expression";

const char* const kDisableReport =
    "triggered of the sequence 'e4', which has no explicit clocking event, "
    "may not stand in a disable condition";

TEST(MethodClockInferenceElab,
     DISABLED_AClockedActualOnItsFormalsClockIsAccepted) {
  ExpectAccepted(
      "  sequence e6(f); @(posedge clk_e) f; endsequence\n"
      "  a3: assert property (@(posedge clk_a) a |=> e6(h4.triggered));\n");
}

TEST(MethodClockInferenceElab,
     DISABLED_AClocklessSequenceInADefaultDisableIsReported) {
  ElabFixture f;
  std::string src = InferenceDesign(
      "  default clocking cb @(posedge clk_a); endclocking\n"
      "  default disable iff (e4.triggered);\n"
      "  a1: assert property (a);\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDisableReport,
                            LineHolding(src, "default disable"), "16.13.6"));
  EXPECT_EQ(CountHolding(f.diag.Diagnostics(), kDisableReport), 1u);
}

TEST(MethodClockInferenceElab, AClockedSequenceInADefaultDisableIsAccepted) {
  ExpectAccepted(
      "  default clocking cb @(posedge clk_a); endclocking\n"
      "  default disable iff (g4.triggered);\n"
      "  a1: assert property (a);\n");
}

TEST(MethodClockInferenceElab,
     DISABLED_AClocklessSequenceInAClockExpressionIsReported) {
  ElabFixture f;
  std::string src = InferenceDesign(
      "  a1: assert property (@(posedge clk_a iff e4.triggered) a);\n"
      "  a2: assert property (@(e4.triggered) a);\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClockExpressionReport,
                            LineHolding(src, "a1:"), "16.13.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClockExpressionReport,
                            LineHolding(src, "a2:"), "16.13.6"));
}

TEST(MethodClockInferenceElab, AClockedSequenceInAClockExpressionIsAccepted) {
  ExpectAccepted(
      "  a1: assert property (@(posedge clk_a iff g4.triggered) a);\n"
      "  a2: assert property (@(g4.triggered) a);\n");
}

const char* const kUsesOutsideAnAssertion =
    "  initial begin wait (e4.triggered); $display(\"x\"); end\n"
    "  always @(e4) $display(\"y\");\n";

TEST(MethodClockInferenceElab, DISABLED_AUseWithNoClockToInferIsReported) {
  ElabFixture f;
  std::string src = InferenceDesign(kUsesOutsideAnAssertion);
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            std::string("the sequence 'e4' ") + kNoClockReport,
                            LineHolding(src, "wait (e4"), "16.13.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            std::string("the sequence 'e4' ") + kNoClockReport,
                            LineHolding(src, "@(e4)"), "16.13.6"));
}

TEST(MethodClockInferenceElab, TheSameUsesUnderADefaultClockingAreAccepted) {
  ExpectAccepted(std::string("  default clocking cb @(posedge clk_a); "
                             "endclocking\n") +
                 kUsesOutsideAnAssertion);
}

TEST(InferredClockFormalElab,
     DISABLED_AnExplicitActualEqualToTheContextsClock) {
  ExpectAccepted(
      "  a1: assert property (@(posedge clk_a) a |=> "
      "f4(posedge clk_a).triggered);\n");
}

TEST(InferredClockFormalElab,
     DISABLED_AnExplicitActualOtherThanTheContextsClock) {
  ElabFixture f;
  std::string src = InferenceDesign(
      "  a1: assert property (@(posedge clk_a) a |=> "
      "f4(posedge clk_d).triggered);\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the ending clock of 'f4' differs from the clock "
                            "of the context its triggered stands in",
                            LineHolding(src, "a1:"), "16.9.11"));
}

TEST(InferredClockFormalElab,
     DISABLED_ADefaultLeftInADisableConditionIsReported) {
  ElabFixture f;
  std::string src = InferenceDesign(
      "  a1: assert property (@(posedge clk_a) disable iff (f4.triggered) "
      "a);\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "f4", LineHolding(src, "a1:"),
                            "16.13.6"));
}

TEST(InferredClockFormalElab, DISABLED_ADefaultWhereNoClockResolvesIsReported) {
  ElabFixture f;
  std::string src = InferenceDesign(
      "  initial begin wait (f4.triggered); $display(\"x\"); end\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "no clock can be inferred for the $inferred_clock "
                            "formal 'ck' of the sequence 'f4'",
                            LineHolding(src, "wait (f4"), "16.14.7"));
}

TEST(InferredClockFormalElab, DISABLED_EachUseWhereAClockResolvesIsAccepted) {
  ExpectAccepted(
      "  default clocking cb @(posedge clk_d); endclocking\n"
      "  initial begin wait (f4.triggered); $display(\"x\"); end\n"
      "  always @(posedge clk_a) if (f4.triggered) $display(\"y\");\n"
      "  a1: assert property (@(posedge clk_a) a |=> f4.triggered);\n"
      "  sequence s2; @(posedge clk_a) a ##1 f4.triggered; endsequence\n"
      "  sequence d2; @(posedge clk_e) a ##1 f4.matched; endsequence\n"
      "  initial begin @(f4); $display(\"z\"); end\n");
}

TEST(PortSequenceActualElab,
     DISABLED_AClocklessSequenceOnAPortWithNoDefaultIsReported) {
  ElabFixture f;
  std::string src =
      "module mod_adder(input logic x);\n"
      "endmodule\n" +
      InferenceDesign("  mod_adder u1(e4.triggered);\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            std::string("the sequence 'e4' ") + kNoClockReport,
                            LineHolding(src, "u1("), "16.13.6"));
}

TEST(PortSequenceActualElab, AClockedSequenceOnAPortWithNoDefaultIsAccepted) {
  ElabFixture f;
  std::string src =
      "module mod_adder(input logic x);\n"
      "endmodule\n" +
      InferenceDesign("  mod_adder u1(g4.triggered);\n");
  ElaborateSrc(src, f);
  EXPECT_EQ(ErrorCount(f.diag.Diagnostics()), 0u);
}

}  // namespace
