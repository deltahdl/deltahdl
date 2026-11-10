#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(DollarConstantSimulation, UnboundedParameterRegisteredDuringLowering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = $;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_TRUE(f.ctx.IsUnboundedParam("P"));
}

TEST(DollarConstantSimulation, ChainedDollarParameterRegisteredAsUnbounded) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter Q = $;\n"
      "  parameter P = Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_TRUE(f.ctx.IsUnboundedParam("Q"));
  EXPECT_TRUE(f.ctx.IsUnboundedParam("P"));
}

TEST(DollarConstantSimulation, BoundedParameterNotRegisteredAsUnbounded) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_FALSE(f.ctx.IsUnboundedParam("P"));
}

TEST(DollarConstantSimulation, IsunboundedReadsEveryKindOfParameterName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk; parameter PB = 3; endpackage\n"
                 "module sub; parameter S = $; endmodule\n"
                 "module t #(parameter int mx = $) ();\n"
                 "  parameter r2 = $;\n"
                 "  parameter Q = r2;\n"
                 "  sub s();\n"
                 "  initial $display(\"%b %b %b %b %b\", $isunbounded(s.S),\n"
                 "    $isunbounded(Q), $isunbounded(r2), $isunbounded(mx),\n"
                 "    $isunbounded(pk::PB));\n"
                 "endmodule\n",
                 f),
      "1 1 1 1 0\n");
}

TEST(DollarConstantSimulation,
     DISABLED_IsunboundedOfAPackageParameterHoldingDollar) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk; parameter PU = $; endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%b\", $isunbounded(pk::PU));\n"
                       "endmodule\n",
                       f),
            "1\n");
}

TEST(DollarConstantSimulation, DISABLED_IsunboundedChoosesAGenerateBranch) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module c #(parameter int max_quiet = 0, parameter int at = 0) ();\n"
          "  if (!$isunbounded(max_quiet) && (max_quiet == 0)) begin : z\n"
          "    initial #at $display(\"quiet\");\n"
          "  end else if ($isunbounded(max_quiet)) begin : u\n"
          "    initial #at $display(\"unbounded\");\n"
          "  end else begin : b\n"
          "    initial #at $display(\"bounded %0d\", max_quiet);\n"
          "  end\n"
          "endmodule\n"
          "module t;\n"
          "  c u1();\n"
          "  c #(.max_quiet($), .at(1)) u2();\n"
          "  c #(.max_quiet(4), .at(2)) u3();\n"
          "endmodule\n",
          f),
      "quiet\nunbounded\nbounded 4\n");
}

TEST(DollarConstantSimulation,
     ClauseExampleBoundsADelayRangeWithADollarParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter r2 = $;\n"
                       "  logic clk = 0, a = 0, b = 0, c = 0, d = 0;\n"
                       "  property inq1(r1, r2);\n"
                       "    @(posedge clk) a ##[r1:r2] b ##1 c |=> d;\n"
                       "  endproperty\n"
                       "  assert property (inq1(3, r2));\n"
                       "  initial $display(\"%b\", $isunbounded(r2));\n"
                       "endmodule\n",
                       f),
            "1\n");
}

}  // namespace
