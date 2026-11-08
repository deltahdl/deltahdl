#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceExprElaboration, CycleDelayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b ##2 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, RangedDelayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, gnt;\n"
      "  sequence req_gnt;\n"
      "    @(posedge clk) req ##[1:5] gnt;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, ParenthesizedSequenceWithRepetitionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, UnboundedDelayWithDollarElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, ack;\n"
      "  property p;\n"
      "    @(posedge clk) req |-> ##[0:$] ack;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElaboration, ParameterAndActualBoundsAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  localparam int LO = 3, HI = 1, NEG = -1;\n"
      "  sequence s(int d);\n"
      "    a ##d b;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) a ##[LO:HI] b);\n"
      "  a2: assert property (@(posedge clk) s(NEG));\n"
      "  a3: assert property (@(posedge clk) s(LO));\n"
      "  a4: assert property (@(posedge clk) a ##[HI:LO] b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the maximum of a cycle delay range shall be no "
                            "less than its minimum",
                            7, "16.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cycle delay shall be 0 or greater", 5, "16.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the maximum of a cycle delay range", 10, "16.7"));
}

TEST(CycleDelayElaboration, ABoundLedByALiteralIsFoldedWhole) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  a1: assert property (@(posedge clk) a ##[2+1:1] b);\n"
      "  a2: assert property (@(posedge clk) a ##[1+1:3] b);\n"
      "  sequence s;\n"
      "    a ##[1:4-5] b;\n"
      "  endsequence\n"
      "  a3: assert property (@(posedge clk) s);\n"
      "  a4: assert property (@(posedge clk) a ##[1:5-4] b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the maximum of a cycle delay range shall be no "
                            "less than its minimum",
                            3, "16.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the maximum of a cycle delay range", 4, "16.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cycle delay shall be 0 or greater", 6, "16.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a cycle delay shall be 0 or greater", 9, "16.7"));
}

}  // namespace
