#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SysTaskTime, ReportsZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial $display(\"%0d\", $time);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(SysTaskTime, ScalesAndRoundsUpLikeLrmExample) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

TEST(SysTaskTime, ScalesAndRoundsDownLikeLrmExample) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    #1.6;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

TEST(SysTaskTime, RoundsHalfwayValueUp) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.5;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

TEST(SysTaskTime, InvokingModuleUnitControlsScaling) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #16;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "16\n");
}

TEST(SysTaskTime, ScalesAcrossMultipleDecades) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #3.6;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(SysTaskTime, ReturnsFull64BitTimeNotTruncated) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd4294967297);\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4294967297\n");
}

TEST(SysTaskTime, ScaledValueFlowsThroughProceduralAssignment) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  integer captured;\n"
      "  initial begin\n"
      "    #1.6 captured = $time;\n"
      "    $display(\"%0d\", captured);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

TEST(SysTaskTime, ScaledValueUsedAsComparisonOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    if ($time == 2) $display(\"scaled_match\");\n"
      "    if ($time == 16) $display(\"unscaled_match\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scaled_match\n");
}

TEST(SysTaskTime, HierarchicallyCalledFunctionReadsItsModulesUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  function longint time_in_a(); return $time; endfunction\n"
      "  initial #10 $display(\"a %0d\", time_in_a());\n"
      "endmodule\n"
      "module b;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  a ia();\n"
      "  initial #10 $display(\"b %0d\", ia.time_in_a());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a 10\nb 10000\n");
}

TEST(SysTaskTime, APackagesSubroutinesRunInThePackagesTimeUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  timeunit 1ps / 1ps;\n"
                       "  class C;\n"
                       "    function void show();\n"
                       "      $display(\"cls %0d %f\", $time, $realtime);\n"
                       "    endfunction\n"
                       "    task wait3(); #3; endtask\n"
                       "  endclass\n"
                       "  function void fshow();\n"
                       "    $display(\"fn %0d\", $time);\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module t;\n"
                       "  timeunit 1ns / 1ps;\n"
                       "  initial begin\n"
                       "    automatic p::C c = new;\n"
                       "    #3;\n"
                       "    c.show();\n"
                       "    p::fshow();\n"
                       "    c.wait3();\n"
                       "    $display(\"after %0d %f\", $time, $realtime);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cls 3000 3000.000000\nfn 3000\nafter 3 3.003000\n");
}

}  // namespace
