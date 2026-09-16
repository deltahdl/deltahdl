#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's ALU around the statements given, as
// test/src/e2e/restrict_statement.sv is: clk rises at 5, 15, 25, 35 and
// 45, ctr is high across the ticks of 25 and 35, so the ALU subtracts at
// those two ticks and adds at the other three, and the run ends at 50.
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

// §16.14.4: a restrict property statement is not verified in simulation, so
// the clause's restriction of ctr to 0 reports nothing at the ticks ctr is
// 1, and that the ALU subtracts there is not an error.
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

// §16.14.4: the restrict has the semantics of assume property apart from its
// not being verified in simulation, so the same property assumed is checked
// and fails at the two ticks ctr is 1, while the restriction beside it adds
// no failure to them.
TEST(RestrictStatementRun, TheAssumeOfTheSamePropertyIsVerified) {
  SimFixture f;
  RunAndFindVar(AluSource("  restrict property (@(posedge clk) ctr == '0);\n"
                          "  assumed: assume property (@(posedge clk) ctr == "
                          "'0);\n"),
                f, "subs");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 2);
}

// §16.14.4: the statement has no action block, and it is not verified
// whatever the form of its property_spec: the instance of a named property
// and a temporal property the tick of 35 would fail report nothing, and
// neither draws the report an unevaluated assertion draws, since here not
// evaluating is the rule.
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
