#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around the clause's property abc and one assert statement over
// it, as test/src/e2e/assert_statement.sv is: clk rises at 5, 15, ..., 75;
// in1 is high at 15 and in2 at 25, so the attempt of 15 fails at 25; in1
// is high at 35 and in2 at 45, with rst 2 across 45; the run ends at 80.
std::string AssertSource(const std::string& statement) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int rst = 0;\n"
         "  logic in1 = 0, in2 = 0;\n"
         "  int passes = 0, fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  property abc(a, b, c);\n"
         "    disable iff (a==2) @(posedge clk) not (b ##1 c);\n"
         "  endproperty\n" +
         statement +
         "  initial begin\n"
         "    #10 in1 = 1;\n"
         "    #10 in1 = 0; in2 = 1;\n"
         "    #10 in2 = 0; in1 = 1;\n"
         "    #8 rst = 2;\n"
         "    #2 in1 = 0; in2 = 1;\n"
         "    #8 rst = 0;\n"
         "    #2 in2 = 0;\n"
         "    #30 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// §16.14.1: the pass statements run where the property is true and the
// fail statements where it is false, and a disabled evaluation runs
// neither: the attempt of 35 would fail at 45 and is disabled there.
TEST(AssertStatementRun,
     PassAndFailStatementsFollowTheVerdictAndADisabledAttemptRunsNeither) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AssertSource("  env_prop: assert property (abc(rst, in1, in2))\n"
                   "    passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.14.1: with the else clause omitted the tool calls $error where the
// property fails, once, at 25; a null pass statement is no action.
TEST(AssertStatementRun, WithoutAnElseClauseTheToolReportsTheFailure) {
  SimFixture f;
  std::string out = RunCapture(
      AssertSource("  env_prop: assert property (abc(rst, in1, in2))\n"
                   "    ;\n"),
      f);
  EXPECT_EQ(out, "$finish at time 80\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

// §16.14.1: the action block may hold an immediate assertion, which runs
// with the fail statement, in the Reactive region, where it reads the
// value the variables then hold.
TEST(AssertStatementRun, AnImmediateAssertionMayStandInTheActionBlock) {
  SimFixture f;
  std::string out = RunCapture(
      AssertSource("  env_prop: assert property (abc(rst, in1, in2))\n"
                   "    else assert (in2 == 1)\n"
                   "      $display(\"immediate passed at %0d\", $time);\n"),
      f);
  EXPECT_EQ(out, "immediate passed at 25\n$finish at time 80\n");
}

// §16.14.1: the pass and fail statements run in the Reactive region, after
// the Active region of the tick, so a pass statement sees what an always
// procedure wrote at the tick.
TEST(AssertStatementRun, TheActionBlockRunsInTheReactiveRegion) {
  SimFixture f;
  auto* seen = RunAndFindVar(
      AssertSource("  int marker = 0, seen = 0;\n"
                   "  always @(posedge clk) marker = $time;\n"
                   "  reactive: assert property (@(posedge clk) 1)\n"
                   "    if (marker == $time) seen++;\n"),
      f, "seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 8u);
}

}  // namespace
