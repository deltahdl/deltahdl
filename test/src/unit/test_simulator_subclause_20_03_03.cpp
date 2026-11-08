#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SysTaskRealtime, ReportsZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial $display(\"%g\", $realtime);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(SysTaskRealtime, ScalesToRealFractionSecondValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    #1.6;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3.2\n");
}

TEST(SysTaskRealtime, KeepsFractionThatTimeRoundsAway) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    $display(\"%0d %g\", $time, $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1.6\n");
}

TEST(SysTaskRealtime, InvokingModuleUnitControlsScaling) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #16;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "16\n");
}

TEST(SysTaskRealtime, ScalesWhenUnitFromCombinedTimeunitDecl) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns / 1ns;\n"
      "  initial begin\n"
      "    #2.3;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2.3\n");
}

TEST(SysTaskRealtime, ScalesAcrossMultipleDecades) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2.5;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2.5\n");
}

TEST(SysTaskRealtime, RealValueFlowsThroughProceduralAssignment) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  real captured;\n"
      "  initial begin\n"
      "    #1.6 captured = $realtime;\n"
      "    $display(\"%g\", captured);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1.6\n");
}

TEST(SysTaskRealtime, RealValueUsedAsComparisonOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2.5;\n"
      "    if ($realtime == 2.5) $display(\"scaled_match\");\n"
      "    if ($realtime == 25) $display(\"unscaled_match\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scaled_match\n");
}

}  // namespace
