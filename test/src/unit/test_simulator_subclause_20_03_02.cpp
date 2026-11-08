#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SysTaskStime, ReportsZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial $display(\"%0d\", $stime);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(SysTaskStime, ScaledToInvokingModuleUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

TEST(SysTaskStime, InvokingModuleUnitControlsScaling) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #20;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "20\n");
}

TEST(SysTaskStime, ScalesWhenUnitFromCombinedTimeunitDecl) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns / 1ns;\n"
      "  initial begin\n"
      "    #3;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

TEST(SysTaskStime, TruncatesToLow32BitsUnlikeTime) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd4294967301);\n"
      "    $display(\"%0d %0d\", $time, $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4294967301 5\n");
}

TEST(SysTaskStime, WrapsToZeroAtExact32BitBoundary) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd4294967296);\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(SysTaskStime, ScalesLargeTimeBeforeTruncating) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #500000000;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "500000000\n");
}

TEST(SysTaskStime, ReportsFullUnsigned32BitRange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd2147483649);\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2147483649\n");
}

TEST(SysTaskStime, ScaledValueFlowsThroughProceduralAssignment) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  integer captured;\n"
      "  initial begin\n"
      "    #2 captured = $stime;\n"
      "    $display(\"%0d\", captured);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

TEST(SysTaskStime, ScaledValueUsedAsComparisonOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2;\n"
      "    if ($stime == 2) $display(\"scaled_match\");\n"
      "    if ($stime == 20) $display(\"unscaled_match\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scaled_match\n");
}

}  // namespace
