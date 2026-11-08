#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(DesignTimingCheckEvaluation, SetupViolationInARunIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 23);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #31 d = 1'b1;\n"
      "    #9 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), "$setup violation: data signal",
                      LineHolding(kDesign, "$setup(d, posedge clk"), "31.3.1"));
}

TEST(DesignTimingCheckEvaluation, SetupSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      DrivenToCompletion("module top(\n"
                         "    output logic d,\n"
                         "    output logic clk);\n"
                         "  specify\n"
                         "    $setup(d, posedge clk, 23);\n"
                         "  endspecify\n"
                         "  initial begin\n"
                         "    d = 1'b0;\n"
                         "    clk = 1'b0;\n"
                         "    #11 d = 1'b1;\n"
                         "    #63 clk = 1'b1;\n"
                         "  end\n"
                         "endmodule\n",
                         f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

TEST(DesignTimingCheckEvaluation, SetupViolationInARunTogglesTheNotifier) {
  SimFixture f;
  auto* notifier = RunAndFindVar(
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  logic setup_notifier;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 19, setup_notifier);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    setup_notifier = 1'b0;\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #55 d = 1'b1;\n"
      "    #7 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_EQ(notifier->value.ToUint64(), 1u);
}

TEST(DesignTimingCheckEvaluation, HoldViolationInARunIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 17);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #28 clk = 1'b1;\n"
      "    #5 d = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), "$hold violation: data signal",
                      LineHolding(kDesign, "$hold(posedge clk, d"), "31.3.2"));
}

TEST(DesignTimingCheckEvaluation,
     HoldViolationInOneTimeStepWithTheClockAssignedFirst) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 13);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #46 clk = 1'b1;\n"
      "    d = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), "$hold violation: data signal",
                      LineHolding(kDesign, "$hold(posedge clk, d"), "31.3.2"));
}

TEST(DesignTimingCheckEvaluation,
     HoldViolationInOneTimeStepWithTheDataAssignedFirst) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 13);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    clk = 1'b0;\n"
      "    #46 d = 1'b1;\n"
      "    clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), "$hold violation: data signal",
                      LineHolding(kDesign, "$hold(posedge clk, d"), "31.3.2"));
}

TEST(DesignTimingCheckEvaluation, SetupInOneTimeStepReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      DrivenToCompletion("module top(\n"
                         "    output logic d,\n"
                         "    output logic clk);\n"
                         "  specify\n"
                         "    $setup(d, posedge clk, 29);\n"
                         "  endspecify\n"
                         "  initial begin\n"
                         "    d = 1'b0;\n"
                         "    clk = 1'b0;\n"
                         "    #52 d = 1'b1;\n"
                         "    clk = 1'b1;\n"
                         "  end\n"
                         "endmodule\n",
                         f));
  EXPECT_EQ(FindDiag(f, "$setup violation: data signal"), nullptr);
}

TEST(DesignTimingCheckEvaluation, RealLimitIsTimeUnitsOfTheModule) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`timescale 1ns/100ps\n"
                           "module top(output reg clk = 0, output reg d = 0);\n"
                           "  reg n = 0; integer cnt = 0;\n"
                           "  specify\n"
                           "    $setup(d, posedge clk, 2.5, n);\n"
                           "  endspecify\n"
                           "  always @(n) cnt = cnt + 1;\n"
                           "  initial begin\n"
                           "    #10 d = 1;\n"
                           "    #2.4 clk = 1;\n"
                           "    #5 clk = 0;\n"
                           "    #2.6 d = 0;\n"
                           "    #2.5 clk = 1;\n"
                           "    #5 $display(\"%0d\", cnt);\n"
                           "  end\n"
                           "endmodule\n",
                           f),
      "1\n");
}

TEST(DesignTimingCheckEvaluation, LimitIsInTheDeclaringModulesUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns/1ns\n"
                                 "module dut(input clk, input d);\n"
                                 "  reg n = 0; integer cnt = 0;\n"
                                 "  specify\n"
                                 "    $setup(d, posedge clk, 5, n);\n"
                                 "  endspecify\n"
                                 "  always @(n) cnt = cnt + 1;\n"
                                 "endmodule\n"
                                 "`timescale 1ps/1ps\n"
                                 "module top;\n"
                                 "  reg clk = 0, d = 0;\n"
                                 "  dut u(.clk(clk), .d(d));\n"
                                 "  initial begin\n"
                                 "    #10000 d = 1; #3000 clk = 1;\n"
                                 "    #8000 clk = 0;\n"
                                 "    #10000 d = 0; #6000 clk = 1;\n"
                                 "    #5000 $display(\"%0d\", u.cnt);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "1\n");
}

}  // namespace
