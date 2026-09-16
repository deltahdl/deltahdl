#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoClockReport =
    "no clock is inferred for the procedural concurrent assertion";

// The clause's r3: no clock is inferred for the context of the always_ff
// whose event control is clock iff reset == 0 or posedge reset, the first
// expression having no edge identifier and reset being referenced within
// the procedure, and in the absence of default clocking that is an error.
TEST(ProceduralClockInference, NoEdgeAndAReferencedSignalInferNoClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clock, input logic reset, input logic d1);\n"
      "  logic q;\n"
      "  int cnt;\n"
      "  property r3;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always_ff @(clock iff reset == 0 or posedge reset) begin\n"
      "    cnt <= reset ? 0 : cnt + 1;\n"
      "    q <= d1;\n"
      "    r3_p: assert property (r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoClockReport, 10, "16.14.6"));
}

// The clause's r4: a delay is a blocking timing control and a second event
// control is one too many, so no clock is inferred for the always procedure
// and the assertion is reported.
TEST(ProceduralClockInference, ADelayAndASecondEventControlInferNoClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic mclk, input logic d1);\n"
      "  logic q, q1;\n"
      "  property r4;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always @(posedge mclk) begin\n"
      "    #10 q <= d1;\n"
      "    @(negedge mclk)\n"
      "    #10 q1 <= !d1;\n"
      "    r4_p: assert property (r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoClockReport, 10, "16.14.6"));
}

// The clause's r2: posedge clock iff reset == 0 is inferred, reset being
// referenced within the procedure and posedge clock being a proper
// subexpression of the event expression that carries the iff, so the
// assertion is not reported.
TEST(ProceduralClockInference, AnEdgeWithAnIffIsInferredWhole) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clock, input logic reset, input logic d1);\n"
      "  logic q;\n"
      "  int cnt;\n"
      "  property r2;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always_ff @(posedge clock iff reset == 0 or posedge reset) begin\n"
      "    cnt <= reset ? 0 : cnt + 1;\n"
      "    q <= d1;\n"
      "    r2_p: assert property (r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

// §16.14.6: where no clock can be inferred from the procedural context the
// clocks are inferred from the default clocking, as if the assertion were
// instantiated immediately before the procedure, so the clause's r4 under a
// default clocking is not reported; and the clocking event the spec opens
// with needs no inference at all.
TEST(ProceduralClockInference, TheDefaultClockingAndAnOwnClockNeedNoContext) {
  ElabFixture f;
  Elaborate(
      "module m(input logic mclk, input logic scanclk, input logic d1);\n"
      "  logic q, q1;\n"
      "  default clocking dc @(posedge scanclk); endclocking\n"
      "  property r4;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always @(posedge mclk) begin\n"
      "    #10 q <= d1;\n"
      "    r4_p: assert property (r4);\n"
      "    r4_own: assert property (@(posedge mclk) r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
