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

}  // namespace
