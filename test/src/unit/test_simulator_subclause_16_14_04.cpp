#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string AluSource(const std::string& statements) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic ctr = 0;\n"
         "  logic [7:0] a = 8'd12, b = 8'd5, y = 8'd0;\n"
         "  int adds = 0, subs = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) begin\n"
         "    y = ctr ? a - b : a + b;\n"
         "    if (ctr) subs++;\n"
         "    else adds++;\n"
         "  end\n"
         "  property addition;\n"
         "    @(posedge clk) ctr == '0;\n"
         "  endproperty\n" +
         statements +
         "  initial begin\n"
         "    #20 ctr = 1;\n"
         "    #20 ctr = 0;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(RestrictStatementRun, ARestrictWhosePropertyFailsReportsNoFailure) {
  SimFixture f;
  std::string out = RunCapture(
      AluSource("  restrict property (@(posedge clk) ctr == '0);\n"), f);
  EXPECT_EQ(out, "$finish at time 50\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* subs = f.ctx.FindVariable("subs");
  ASSERT_NE(subs, nullptr);
  EXPECT_EQ(subs->value.ToUint64(), 2u);
  auto* adds = f.ctx.FindVariable("adds");
  ASSERT_NE(adds, nullptr);
  EXPECT_EQ(adds->value.ToUint64(), 3u);
}

TEST(RestrictStatementRun, TheAssumeOfTheSamePropertyIsVerified) {
  SimFixture f;
  RunAndFindVar(AluSource("  restrict property (@(posedge clk) ctr == '0);\n"
                          "  assumed: assume property (@(posedge clk) ctr == "
                          "'0);\n"),
                f, "subs");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 2);
}

TEST(RestrictStatementRun, ANamedInstanceAndATemporalRestrictReportNothing) {
  SimFixture f;
  std::string out = RunCapture(
      AluSource("  named_restriction: restrict property (addition);\n"
                "  temporal_restriction: restrict property\n"
                "    (@(posedge clk) ctr |=> !ctr);\n"),
      f);
  EXPECT_EQ(out, "$finish at time 50\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
