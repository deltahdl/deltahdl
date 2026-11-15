#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "helpers_expect_runs.h"

using namespace delta;

namespace {

struct ErrorRun {
  int errors;
  std::string out;
};

ErrorRun RunCountingErrors(const std::string& src) {
  SimFixture f;
  testing::internal::CaptureStderr();
  std::string out = RunCapture(src, f);
  std::string err = testing::internal::GetCapturedStderr();
  int errors = 0;
  for (std::size_t at = err.find("ERROR"); at != std::string::npos;
       at = err.find("ERROR", at + 1)) {
    ++errors;
  }
  return {errors, out};
}

constexpr const char* kFailingExpect =
    "    expect (@(posedge clk) c);\n"
    "    $display(\"after at %0d\", $time);\n";

constexpr const char* kAfterFailure = "after at 25\n$finish at time 210\n";

int ErrorsUnder(const std::string& controls) {
  ErrorRun run = RunCountingErrors(
      ExpectDesign(controls + kFailingExpect,
                   "  module other;\n  endmodule\n  other o();\n"));
  EXPECT_EQ(run.out, kAfterFailure) << controls;
  return run.errors;
}

TEST(ExpectDefaultErrorRun, AnElseClauseOnlyRunsInsteadOfTheError) {
  ErrorRun run = RunCountingErrors(
      ExpectDesign("    expect (@(posedge clk) c)\n"
                   "      else $display(\"fail at %0d\", $time);\n"));
  EXPECT_EQ(run.errors, 0);
  EXPECT_EQ(run.out, "fail at 25\n$finish at time 210\n");
}

TEST(ExpectDefaultErrorRun, APassStatementOnlyFailingReportsTheError) {
  ErrorRun run = RunCountingErrors(
      ExpectDesign("    expect (@(posedge clk) c)\n"
                   "      $display(\"pass at %0d\", $time);\n"
                   "    $display(\"after at %0d\", $time);\n"));
  EXPECT_EQ(run.errors, 1);
  EXPECT_EQ(run.out, kAfterFailure);
}

TEST(ExpectDefaultErrorRun, APassStatementOnlySucceedingReportsNoError) {
  ErrorRun run = RunCountingErrors(
      ExpectDesign("    expect (@(posedge clk) a ##1 b)\n"
                   "      $display(\"pass at %0d\", $time);\n"));
  EXPECT_EQ(run.errors, 0);
  EXPECT_EQ(run.out, "pass at 35\n$finish at time 210\n");
}

TEST(ExpectDefaultErrorRun, FailOffNamingExpectStatementsSuppressesIt) {
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(9, 16);\n"), 0);
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(9, 15);\n"), 1);
}

TEST(ExpectDefaultErrorRun, FailOffWithTheDefaultTypeSuppressesIt) {
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(9);\n"), 0);
}

TEST(ExpectDefaultErrorRun, FailOffWithAMaskHoldingTheExpectBitSuppressesIt) {
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(9, 17);\n"), 0);
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(9, 1);\n"), 1);
}

TEST(ExpectDefaultErrorRun, AssertFailOffSuppressesIt) {
  EXPECT_EQ(ErrorsUnder("    $assertfailoff;\n"), 0);
}

TEST(ExpectDefaultErrorRun, AssertFailOffOnTheHoldingScopeSuppressesIt) {
  EXPECT_EQ(ErrorsUnder("    $assertfailoff(0, m);\n"), 0);
  EXPECT_EQ(ErrorsUnder("    $assertfailoff(0, o);\n"), 1);
}

TEST(ExpectDefaultErrorRun, FailOnAfterFailOffRestoresIt) {
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(9, 16);\n"
                        "    $assertcontrol(8, 16);\n"),
            1);
  EXPECT_EQ(ErrorsUnder("    $assertfailoff;\n    $assertfailon;\n"), 1);
}

TEST(ExpectDefaultErrorRun, ALockKeepsFailOffFromSuppressingIt) {
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(1, 16);\n"
                        "    $assertcontrol(9, 16);\n"),
            1);
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(1, 16);\n"
                        "    $assertcontrol(2, 16);\n"
                        "    $assertcontrol(9, 16);\n"),
            0);
}

TEST(ExpectDefaultErrorRun, OffAndKillLeaveItReported) {
  EXPECT_EQ(ErrorsUnder("    $assertoff;\n"), 1);
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(4, 16);\n"), 1);
  EXPECT_EQ(ErrorsUnder("    $assertkill;\n"), 1);
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(5, 16);\n"), 1);
}

TEST(ExpectDefaultErrorRun, PassOffLeavesItReported) {
  EXPECT_EQ(ErrorsUnder("    $assertcontrol(7, 16);\n"), 1);
}

constexpr const char* kPlacedExpect = "expect (@(posedge clk) c);\n";

int ErrorsPlaced(const std::string& body, const std::string& declarations,
                 const std::string& before = "") {
  ErrorRun run = RunCountingErrors(before + ExpectDesign(body, declarations));
  EXPECT_EQ(run.out, "$finish at time 210\n") << declarations;
  return run.errors;
}

TEST(ExpectDefaultErrorRun, EachPlaceReportsItOnce) {
  EXPECT_EQ(ErrorsPlaced("    tf();\n", std::string("  task automatic tf();\n"
                                                    "    ") +
                                            kPlacedExpect + "  endtask\n"),
            1);
  EXPECT_EQ(
      ErrorsPlaced(
          std::string("    fork\n      ") + kPlacedExpect + "    join\n", ""),
      1);
  EXPECT_EQ(
      ErrorsPlaced("", std::string("  interface ifc;\n"
                                   "    initial begin\n      #20;\n      ") +
                           kPlacedExpect +
                           "    end\n  endinterface\n  ifc u();\n"),
      1);
  EXPECT_EQ(ErrorsPlaced(
                "", std::string("  program pr;\n"
                                "    initial begin\n      #20;\n      ") +
                        kPlacedExpect + "      #200;\n    end\n  endprogram\n"),
            1);
  EXPECT_EQ(ErrorsPlaced("    h.run();\n",
                         std::string("  class C;\n    task run();\n      ") +
                             kPlacedExpect +
                             "    endtask\n  endclass\n  C h = new;\n"),
            1);
  EXPECT_EQ(
      ErrorsPlaced("    pk::pt();\n", "  always #5 pk::pclk = ~pk::pclk;\n",
                   "package pk;\n  logic pclk = 0, pc = 0;\n"
                   "  task automatic pt();\n"
                   "    expect (@(posedge pclk) pc);\n"
                   "  endtask\nendpackage\n"),
      1);
  EXPECT_EQ(
      ErrorsPlaced("", std::string("  if (1) begin : g\n"
                                   "    initial begin\n      #20;\n      ") +
                           kPlacedExpect + "    end\n  end\n"),
      1);
}

}  // namespace
