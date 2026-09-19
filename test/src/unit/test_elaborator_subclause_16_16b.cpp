#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoClockReport =
    "concurrent assertion has no leading clocking event";

// §16.16 (f): with no default clocking, the clause's c1 covers a sequence
// declared with no clock and its a6 asserts a property with none, so
// neither has an explicit, inferred or default leading clocking event and
// each is illegal.
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

// §16.16 (f): the clause's c3 covers s3, an instance of a sequence declared
// with negedge clk, from which a unique leading clocking event is
// determined, so it is legal; its c4 covers s3 ##1 b, whose maximal
// property is no instance, so it is not.
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

// §16.16 (c): a contextually inferred clocking event is the leading
// clocking event of the assertion it applies to, which a multiclocked
// property may not take: the clause's a3 asserts $fell(c) |=> q2, q2
// clocked by posedge clk, in an always at negedge clk.
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

// §16.16 (a) and (b): under a default clocking an unclocked spec, an
// instance of an unclocked property and an instance of a property declared
// in the clocking block, named through the block, are all legal.
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

// §16.16 (f) and §16.9.5: a sequence declared with posedge clk over a
// parenthesised `and` of two concatenations, the composite ending at the
// later end point, followed by `##0 e`, a shape the linear monitor does not
// read, still determines a unique leading clocking event, so an assertion
// whose maximal property is an instance of it is legal.
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

// §16.16 (f) and §16.7: the same with each concatenation over a
// cycle_delay_range, `##[1:6]` and `##[1:9]`.
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

// §16.16 (f): the same body declared with no clocking event, under no
// default clocking, determines none, so the assertion instantiating it is
// reported.
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

}  // namespace
