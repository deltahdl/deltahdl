#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoClockReport =
    "concurrent assertion has no leading clocking event";

TEST(ClockResolutionElaboration, NoClockAnywhereIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module examples_without_default(input logic a, b, c, clk);\n"
      "  property q1;\n"
      "    $rose(a) |-> ##[1:5] b;\n"
      "  endproperty\n"
      "  sequence s2;\n"
      "    $rose(a) ##[1:5] b;\n"
      "  endsequence\n"
      "  a6: assert property ($fell(c) |=> q1);\n"
      "  c1: cover property (s2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 8, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 9, "16.16"));
}

TEST(ClockResolutionElaboration, AnInstanceDeterminesTheClockAndMoreDoesNot) {
  ElabFixture f;
  Elaborate(
      "module examples_without_default(input logic a, b, clk);\n"
      "  sequence s2;\n"
      "    $rose(a) ##[1:5] b;\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    @(negedge clk) s2;\n"
      "  endsequence\n"
      "  c3: cover property (s3);\n"
      "  c4: cover property (s3 ##1 b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 8, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 9, "16.16"));
}

TEST(ClockResolutionElaboration,
     AMulticlockedPropertyMayNotTakeAnInferredClock) {
  ElabFixture f;
  Elaborate(
      "module examples_with_default(input logic a, b, c, clk);\n"
      "  property q1;\n"
      "    $rose(a) |-> ##[1:5] b;\n"
      "  endproperty\n"
      "  property q2;\n"
      "    @(posedge clk) q1;\n"
      "  endproperty\n"
      "  default clocking posedge_clk @(posedge clk);\n"
      "  endclocking\n"
      "  always @(negedge clk) begin\n"
      "    a1: assert property ($fell(c) |=> q1);\n"
      "    a3: assert property ($fell(c) |=> q2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a multiclocked property may not take a "
                             "contextually inferred leading clocking event",
                             11, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a multiclocked property may not take a "
                            "contextually inferred leading clocking event",
                            12, "16.16"));
}

TEST(ClockResolutionElaboration, TheDefaultAndTheBlockClockTheRest) {
  ElabFixture f;
  Elaborate(
      "module examples_with_default(input logic a, b, c, clk);\n"
      "  property q1;\n"
      "    $rose(a) |-> ##[1:5] b;\n"
      "  endproperty\n"
      "  default clocking posedge_clk @(posedge clk);\n"
      "    property q3;\n"
      "      $fell(c) |=> q1;\n"
      "    endproperty\n"
      "  endclocking\n"
      "  a1: assert property (q1);\n"
      "  a2: assert property ($fell(c) |=> q1);\n"
      "  a3: assert property (posedge_clk.q3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(ClockResolutionElaboration,
     AnInstanceOfAConjunctionThenZeroDelayDeterminesTheClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, c, d, e, clk);\n"
      "  sequence s;\n"
      "    @(posedge clk) ((a ##5 b) and (c ##8 d)) ##0 e;\n"
      "  endsequence\n"
      "  assert property (s);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 5, "16.16"));
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockResolutionElaboration,
     AnInstanceOfARangedConjunctionThenZeroDelayDeterminesTheClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, c, d, e, clk);\n"
      "  sequence s;\n"
      "    @(posedge clk) ((a ##[1:6] b) and (c ##[1:9] d)) ##0 e;\n"
      "  endsequence\n"
      "  assert property (s);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 5, "16.16"));
  EXPECT_FALSE(f.has_errors);
}

TEST(ClockResolutionElaboration,
     AnInstanceOfAnUnclockedConjunctionThenZeroDelayIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, c, d, e, clk);\n"
      "  sequence s;\n"
      "    ((a ##5 b) and (c ##8 d)) ##0 e;\n"
      "  endsequence\n"
      "  assert property (s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 5, "16.16"));
}

TEST(ClockResolutionElaboration,
     AnOutsideInstanceInAClockingBlockTakesItsClock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, b;\n"
      "  property q5;\n"
      "    @(negedge clk) b;\n"
      "  endproperty\n"
      "  property q6;\n"
      "    b;\n"
      "  endproperty\n"
      "  clocking cb @(posedge clk);\n"
      "    property q7;\n"
      "      q5;\n"
      "    endproperty\n"
      "    property q8;\n"
      "      q6;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the instance of 'q5' in clocking block 'cb' is "
                            "not clocked on the block's clocking event alone",
                            10, "16.16"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the instance of 'q6' in clocking block 'cb' is "
                             "not clocked on the block's clocking event alone",
                             13, "16.16"));
}

TEST(ClockResolutionElaboration, AnOutsideInstanceOnAnotherClockIsReported) {
  const char* const kReport =
      "is not clocked on the block's clocking event alone";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, clk2, b;\n"
      "  sequence s9;\n"
      "    @(posedge clk2) b;\n"
      "  endsequence\n"
      "  property q10;\n"
      "    @(posedge clk) b;\n"
      "  endproperty\n"
      "  property q11;\n"
      "    @(posedge clk) b |=> @(negedge clk) b;\n"
      "  endproperty\n"
      "  clocking cb @(posedge clk);\n"
      "    property q12;\n"
      "      s9;\n"
      "    endproperty\n"
      "    property q13;\n"
      "      q10;\n"
      "    endproperty\n"
      "    property q14;\n"
      "      q11;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 13, "16.16"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 16, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 19, "16.16"));
}

}  // namespace
