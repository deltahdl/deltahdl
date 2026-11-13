#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

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

constexpr const char* kRestrictSignals =
    "  logic clk = 0, ctr = 1, rst = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  initial #40 $finish;\n";

constexpr PlacedDesign kRestrictDesign = {kRestrictSignals,
                                          "(input logic clk, ctr)", "clk, ctr"};

constexpr const char* kAssumeFailures =
    "[5] ERROR %.a1: Assertion failed.\n"
    "[15] ERROR %.a1: Assertion failed.\n"
    "[25] ERROR %.a1: Assertion failed.\n"
    "[35] ERROR %.a1: Assertion failed.\n";

TEST(RestrictStatementRun, ARestrictIsNotVerifiedInEachPlace) {
  ExpectPlacedLinesInEachPlace(
      kRestrictDesign,
      {"r1: restrict property (@(posedge clk) ctr == '0);\n"
       "r2: restrict property (@(posedge clk) ctr |=> !ctr);\n"
       "a1: assume property (@(posedge clk) ctr == '0);\n",
       kAssumeFailures, "[15] ERROR %.a1: Assertion failed.\n"});
}

TEST(RestrictStatementRun,
     ARestrictWithAClockInferredFromItsProcedureIsNotVerified) {
  SimFixture f;
  PlacedRun run = RunPlaced(PlacedSource(kRestrictDesign, "always",
                                         "r1: restrict property (ctr == '0);\n"
                                         "a1: assume property (ctr == '0);\n"),
                            f);
  EXPECT_EQ(run.lines, PlacedExpected(kAssumeFailures, "t"));
  EXPECT_EQ(f.ctx.AssertionFailCount(), 4);
}

TEST(RestrictStatementRun, ARestrictInEachGenerateLoopIterationIsNotVerified) {
  SimFixture f;
  PlacedRun run =
      RunPlaced("module t;\n" + std::string(kRestrictSignals) +
                    "  for (genvar i = 0; i < 2; i++) begin : gl\n"
                    "    r1: restrict property (@(posedge clk) ctr == '0);\n"
                    "    a1: assume property (@(posedge clk) ctr == '0);\n"
                    "  end\n"
                    "endmodule\n",
                f);
  std::string each_iteration = PlacedExpected(kAssumeFailures, "t.gl[0]") +
                               PlacedExpected(kAssumeFailures, "t.gl[1]");
  EXPECT_EQ(run.lines, PlacedSorted(PlacedLines(each_iteration)));
  EXPECT_EQ(f.ctx.AssertionFailCount(), 8);
}

TEST(RestrictStatementRun,
     ARestrictTakingItsDefaultClockAndDisableConditionIsNotVerified) {
  for (const char* disable : {"", "disable iff (rst) "}) {
    SCOPED_TRACE(disable);
    SimFixture f;
    std::string out =
        RunCapture("module t;\n" + std::string(kRestrictSignals) +
                       "  default clocking @(posedge clk); endclocking\n"
                       "  default disable iff (rst);\n"
                       "  r1: restrict property (" +
                       disable +
                       "ctr == '0);\n"
                       "  a1: assume property (" +
                       disable +
                       "ctr == '0) else "
                       "$display(\"a1 %0t\", $time);\n"
                       "endmodule\n",
                   f);
    EXPECT_EQ(out, "a1 5\na1 15\na1 25\na1 35\n$finish at time 40\n");
    EXPECT_TRUE(f.diag.Diagnostics().empty());
  }
}

}  // namespace
