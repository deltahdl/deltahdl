#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_expect_runs.h"

using namespace delta;

namespace {

constexpr const char* kMatchThenFail =
    "matched at 45\nafter at 45\nfailed at 55\nafter at 55\n"
    "$finish at time 210\n";

void ExpectTwiceOver(const std::string& spec, const std::string& declarations) {
  std::string expect = "    expect (" + spec +
                       ")\n"
                       "      $display(\"matched at %0d\", $time);\n"
                       "      else $display(\"failed at %0d\", $time);\n"
                       "    $display(\"after at %0d\", $time);\n";
  SimFixture f;
  std::string out = RunCapture(ExpectDesign(expect + expect, declarations), f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << spec;
  EXPECT_EQ(out, kMatchThenFail) << spec;
}

TEST(ExpectSpecRun, ANamedPropertyWithoutArguments) {
  ExpectTwiceOver("pn",
                  "  property pn; @(posedge clk) a ##1 b ##1 c; endproperty\n");
}

TEST(ExpectSpecRun, ANamedPropertyWithArguments) {
  ExpectTwiceOver("pa(a, b, c)",
                  "  property pa(x, y, z);\n"
                  "    @(posedge clk) x ##1 y ##1 z;\n"
                  "  endproperty\n");
}

TEST(ExpectSpecRun, ANamedSequenceWithoutArguments) {
  ExpectTwiceOver("sn",
                  "  sequence sn; @(posedge clk) a ##1 b ##1 c; endsequence\n");
}

TEST(ExpectSpecRun, ANamedSequenceWithArguments) {
  ExpectTwiceOver("sa(a, b, c)",
                  "  sequence sa(x, y, z);\n"
                  "    @(posedge clk) x ##1 y ##1 z;\n"
                  "  endsequence\n");
}

std::string Shown(const char* label) {
  return std::string("$display(\"") + label +
         " at %0d data=%0d\", $time, data)";
}

std::string RunAfterObserved(const std::string& body,
                             const std::string& declarations = "") {
  SimFixture f;
  std::string out = RunCapture(ExpectDesign(body, declarations), f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << body;
  return out;
}

TEST(ExpectResumeRun, ASuccessWithPassAndElseReadsTheNbaValue) {
  EXPECT_EQ(RunAfterObserved("    expect (@(posedge clk) a ##1 b) " +
                             Shown("pass") + ";\n      else " + Shown("fail") +
                             ";\n    " + Shown("after") + ";\n"),
            "pass at 35 data=4\nafter at 35 data=4\n$finish at time 210\n");
}

TEST(ExpectResumeRun, ASuccessWithAPassStatementOnlyReadsTheNbaValue) {
  EXPECT_EQ(
      RunAfterObserved("    expect (@(posedge clk) a ##1 b) " + Shown("pass") +
                       ";\n    " + Shown("after") + ";\n"),
      "pass at 35 data=4\nafter at 35 data=4\n$finish at time 210\n");
}

TEST(ExpectResumeRun, AFailureWithPassAndElseReadsTheNbaValue) {
  EXPECT_EQ(RunAfterObserved("    expect (@(posedge clk) c) " + Shown("pass") +
                             ";\n      else " + Shown("fail") + ";\n    " +
                             Shown("after") + ";\n"),
            "fail at 25 data=3\nafter at 25 data=3\n$finish at time 210\n");
}

TEST(ExpectResumeRun, AFailureWithAnElseClauseOnlyReadsTheNbaValue) {
  EXPECT_EQ(
      RunAfterObserved("    expect (@(posedge clk) c) else " + Shown("fail") +
                       ";\n    " + Shown("after") + ";\n"),
      "fail at 25 data=3\nafter at 25 data=3\n$finish at time 210\n");
}

TEST(ExpectResumeRun, AFailureWithANullActionBlockReadsTheNbaValue) {
  SimFixture f;
  std::string out =
      RunCapture(ExpectDesign("    expect (@(posedge clk) c);\n    " +
                              Shown("after") + ";\n"),
                 f);
  EXPECT_EQ(out, "after at 25 data=3\n$finish at time 210\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(ExpectResumeRun, AFirstTickAndALaterTickCompletionReadTheNbaValue) {
  EXPECT_EQ(RunAfterObserved("    #10;\n    expect (@(posedge clk) a) " +
                             Shown("first") + ";\n    #10;\n" +
                             "    expect (@(posedge clk) a ##[1:3] c) " +
                             Shown("later") + ";\n"),
            "first at 35 data=4\nlater at 55 data=6\n$finish at time 210\n");
}

TEST(ExpectResumeRun, AnAutomaticTaskAndItsCallerReadTheNbaValue) {
  EXPECT_EQ(RunAfterObserved("    tw();\n    " + Shown("caller") + ";\n",
                             "  task automatic tw();\n"
                             "    expect (@(posedge clk) a ##1 b) " +
                                 Shown("pass") + ";\n    " + Shown("task") +
                                 ";\n  endtask\n"),
            "pass at 35 data=4\ntask at 35 data=4\ncaller at 35 data=4\n"
            "$finish at time 210\n");
}

TEST(ExpectResumeRun, AProgramsExpectReadsTheModulesNbaValue) {
  EXPECT_EQ(RunAfterObserved(
                "",
                "  program pr;\n    initial begin\n"
                "      #20;\n"
                "      expect (@(posedge clk) a) " +
                    Shown("pass") + "; else " + Shown("fail") + ";\n      " +
                    Shown("after") + ";\n      expect (@(posedge clk) c) " +
                    Shown("pass") + "; else " + Shown("fail") + ";\n      " +
                    Shown("after") + ";\n      #200;\n    end\n  endprogram\n"),
            "pass at 25 data=3\nafter at 25 data=3\nfail at 35 data=4\n"
            "after at 35 data=4\n$finish at time 210\n");
}

std::string PassElseAfter(const std::string& spec) {
  return "    expect (" + spec +
         ")\n"
         "      $display(\"pass at %0d\", $time);\n"
         "      else $display(\"fail at %0d\", $time);\n"
         "    $display(\"after at %0d\", $time);\n";
}

int FailuresOf(const std::string& body, std::string& out) {
  SimFixture f;
  out = RunCapture(ExpectDesign(body), f);
  return f.ctx.AssertionFailCount();
}

TEST(ExpectOneEvaluationRun, ASequenceWithSeveralMatchesPassesOnce) {
  EXPECT_EQ(RunAfterObserved(PassElseAfter("@(posedge clk) a ##[1:3] b")),
            "pass at 35\nafter at 35\n$finish at time 210\n");
}

TEST(ExpectOneEvaluationRun,
     AnImplicationWithSeveralConsequentMatchesPassesOnce) {
  EXPECT_EQ(RunAfterObserved(PassElseAfter("@(posedge clk) a |-> ##[1:5] b")),
            "pass at 35\nafter at 35\n$finish at time 210\n");
}

TEST(ExpectOneEvaluationRun, AnOrSucceededByOneOperandRunsNoLaterElse) {
  EXPECT_EQ(
      RunAfterObserved(PassElseAfter("@(posedge clk) (a ##1 b) or (a ##4 c)")),
      "pass at 35\nafter at 35\n$finish at time 210\n");
}

TEST(ExpectOneEvaluationRun, AnOrSucceededByOneOperandReportsNoLaterError) {
  std::string out;
  EXPECT_EQ(FailuresOf("    expect (@(posedge clk) (a ##1 b) or (a ##4 c));\n"
                       "    $display(\"after at %0d\", $time);\n",
                       out),
            0);
  EXPECT_EQ(out, "after at 35\n$finish at time 210\n");
}

TEST(ExpectOneEvaluationRun, AnAndFailedByOneOperandRunsNothingLater) {
  EXPECT_EQ(RunAfterObserved(
                PassElseAfter("@(posedge clk) (a ##1 !b) and (a ##2 c)")),
            "fail at 35\nafter at 35\n$finish at time 210\n");
}

TEST(ExpectOneEvaluationRun, AnAndFailedWithAPassStatementOnlyReportsOnce) {
  std::string out;
  EXPECT_EQ(FailuresOf("    expect (@(posedge clk) (a ##1 !b) and (a ##2 c))\n"
                       "      $display(\"pass at %0d\", $time);\n"
                       "    $display(\"after at %0d\", $time);\n",
                       out),
            1);
  EXPECT_EQ(out, "after at 35\n$finish at time 210\n");
}

std::string ExpectOf(const std::string& spec, const std::string& label) {
  return "expect (" + spec + ") $display(\"" + label +
         " pass at %0d\", $time);\n      else $display(\"" + label +
         " fail at %0d\", $time);\n";
}

TEST(ExpectFirstTickRun, AnAlwaysBodyReachedAtATickWhereThePropertyHolds) {
  EXPECT_EQ(
      RunAfterObserved("", "  always @(posedge clk) if ($time == 45)\n    " +
                               ExpectOf("@(posedge clk) a", "always")),
      "always fail at 55\n$finish at time 210\n");
}

TEST(ExpectFirstTickRun, AnAlwaysBodyReachedAtATickWhereThePropertyFails) {
  EXPECT_EQ(
      RunAfterObserved("", "  always @(posedge clk) if ($time == 15)\n    " +
                               ExpectOf("@(posedge clk) a", "always")),
      "always pass at 25\n$finish at time 210\n");
}

TEST(ExpectFirstTickRun, AnInitialReachedAtATickAfterAnEventControl) {
  EXPECT_EQ(RunAfterObserved("    repeat (3) @(posedge clk);\n    " +
                             ExpectOf("@(posedge clk) a", "initial")),
            "initial fail at 55\n$finish at time 210\n");
}

TEST(ExpectFirstTickRun, AnUnclockedSpecUnderTheDefaultClocking) {
  EXPECT_EQ(RunAfterObserved("    repeat (3) @(posedge clk);\n    " +
                                 ExpectOf("a", "default"),
                             "  default clocking dcb @(posedge clk);\n"
                             "  endclocking\n"),
            "default fail at 55\n$finish at time 210\n");
}

TEST(ExpectFirstTickRun, AClockingBlockEventClock) {
  EXPECT_EQ(RunAfterObserved(
                "    repeat (3) @(cb);\n    " + ExpectOf("@(cb) a", "block"),
                "  clocking cb @(posedge clk);\n"
                "  endclocking\n"),
            "block fail at 55\n$finish at time 210\n");
}

TEST(ExpectFirstTickRun, AProgramInitialReachedAtATick) {
  EXPECT_EQ(RunAfterObserved("",
                             "  program pr;\n    initial begin\n"
                             "      #40;\n      @(posedge clk);\n      " +
                                 ExpectOf("@(posedge clk) a", "program") +
                                 "      #200;\n    end\n  endprogram\n"),
            "program fail at 55\n$finish at time 210\n");
}

TEST(ExpectFirstTickRun, ReachedAtTimeZeroBeforeTheFirstTick) {
  EXPECT_EQ(RunAfterObserved(
                "", "  initial " + ExpectOf("@(posedge clk) !a", "zero")),
            "zero pass at 5\n$finish at time 210\n");
}

}  // namespace
