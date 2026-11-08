#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoClockReport =
    "no clock is inferred for the procedural concurrent assertion";

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

TEST(ProceduralClockInference, AnAutomaticInTheClockingEventIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  logic clks [2];\n"
      "  always @(a) begin\n"
      "    automatic int k = 1;\n"
      "    a1: assert property (@(posedge clks[k]) a);\n"
      "    a2: assert property (@(posedge clks[0]) a);\n"
      "    a3: assert property (@(posedge clks[0] iff k == 1) a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a clocking event of a procedural concurrent "
                            "assertion may not reference an automatic variable",
                            6, "16.14.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a clocking event of a procedural concurrent "
                            "assertion may not reference an automatic variable",
                            8, "16.14.6"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(),
                    "a clocking event of a procedural concurrent "
                    "assertion may not reference an automatic variable",
                    7, "16.14.6"));
}

}  // namespace
