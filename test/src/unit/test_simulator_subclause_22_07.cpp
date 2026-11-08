#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

TEST(TimescaleSimulation, TimescaleModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(TimescaleSimulation, MultipleTimescaleModulesSimulate) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "module m1;\n"
      "  logic [7:0] unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`timescale 1us / 1ns\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd77;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(TimescaleSimulation, LaterTimescaleOverrideSimulates) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "`timescale 10us / 1us\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(TimescaleSimulation, DirectiveGivesTheModuleAfterItItsUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1us / 1ns\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    $printtimescale;\n"
                                 "    #1 $display(\"%0d\", $time);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "Time scale of (t) is 1us / 1ns\n1\n");
}

TEST(TimescaleSimulation, EachModuleTakesTheDirectiveBeforeIt) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1us / 1ns\n"
                                 "module a;\n"
                                 "  initial $printtimescale;\n"
                                 "endmodule\n"
                                 "`timescale 1ns / 1ps\n"
                                 "module t;\n"
                                 "  a ia();\n"
                                 "  initial #1 $printtimescale;\n"
                                 "endmodule\n",
                                 f),
            "Time scale of (t.ia) is 1us / 1ns\n"
            "Time scale of (t) is 1ns / 1ps\n");
}

TEST(TimescaleSimulation, DelaysAndTimeReadEachModulesOwnUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(
                "`timescale 1ns / 1ns\n"
                "module a;\n"
                "  function longint time_in_a(); return $time; endfunction\n"
                "  initial begin\n"
                "    #10 $display(\"a %0d\", $time);\n"
                "  end\n"
                "endmodule\n"
                "`timescale 1us / 1ns\n"
                "module b;\n"
                "  a ia();\n"
                "  initial begin\n"
                "    #2 $display(\"b %0d\", $time);\n"
                "    #8 $display(\"a %0d\", ia.time_in_a());\n"
                "  end\n"
                "endmodule\n",
                f),
            "a 10\nb 2\na 10000\n");
}

TEST(TimescaleSimulation, CompilationUnitClassTaskWaitsInTheUnitsUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ns\n"
                                 "class Waiter;\n"
                                 "  task wait5(); #5; endtask\n"
                                 "endclass\n"
                                 "`timescale 1us / 1ns\n"
                                 "module t;\n"
                                 "  Waiter w = new;\n"
                                 "  initial begin\n"
                                 "    w.wait5();\n"
                                 "    $display(\"%0.3f\", $realtime);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "0.005\n");
}

TEST(TimescaleSimulation, StructuralAndNonblockingDelaysCountTheUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(
                "`timescale 1ns / 1ps\n"
                "module t;\n"
                "  logic a, n, en;\n"
                "  wire y, z;\n"
                "  trireg #(0, 0, 5) c;\n"
                "  buf #3 g(y, a);\n"
                "  assign #2.5 z = a;\n"
                "  bufif1 (c, a, en);\n"
                "  always @(y) if ($realtime > 10) $display(\"y=%b %g\", y,"
                " $realtime);\n"
                "  always @(z) if ($realtime > 10) $display(\"z=%b %g\", z,"
                " $realtime);\n"
                "  always @(n) if ($realtime > 10) $display(\"n=%b %g\", n,"
                " $realtime);\n"
                "  always @(c) if ($realtime > 10) $display(\"c=%b %g\", c,"
                " $realtime);\n"
                "  initial begin\n"
                "    a = 0; n = 0; en = 1;\n"
                "    #10 a = 1;\n"
                "    n <= #1.5 1;\n"
                "    #1 en = 0;\n"
                "  end\n"
                "endmodule\n",
                f),
            "n=1 11.5\nz=1 12.5\ny=1 13\nc=x 16\n");
}

TEST(TimescaleSimulation, GateDelayCountsItsOwnModulesUnit) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture(
          "`timescale 1us / 1ns\n"
          "module slow(input a, output y);\n"
          "  buf #2 g(y, a);\n"
          "endmodule\n"
          "`timescale 1ns / 1ns\n"
          "module t;\n"
          "  logic a;\n"
          "  wire y;\n"
          "  slow s(a, y);\n"
          "  always @(y) if ($time > 0) $display(\"y=%b %0d\", y, $time);\n"
          "  initial a = 1;\n"
          "endmodule\n",
          f),
      "y=1 2000\n");
}

TEST(TimescaleSimulation, RealDelayRoundsToThePrecision) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`timescale 1ns / 100ps\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    #1.46;\n"
                           "    $display(\"%0.2f %0d\", $realtime, $time);\n"
                           "    $printtimescale;\n"
                           "  end\n"
                           "endmodule\n",
                           f),
      "1.50 2\nTime scale of (t) is 1ns / 100ps\n");
}

TEST(TimescaleSimulation, ClauseExampleRealParameterDelaysAssignments) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 10 ns / 1 ns\n"
                                 "module test;\n"
                                 "  logic set;\n"
                                 "  parameter d = 1.55;\n"
                                 "  initial begin\n"
                                 "    #d set = 0;\n"
                                 "    $display(\"%0.1f\", $realtime);\n"
                                 "    #d set = 1;\n"
                                 "    $display(\"%0.1f\", $realtime);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "1.6\n3.2\n");
  SimFixture g;
  EXPECT_EQ(
      PreprocessAndCapture("`timescale 10 ns / 1 ns\n"
                           "module t;\n"
                           "  parameter d = 1.55;\n"
                           "  parameter real e = 1.55;\n"
                           "  real r = 1.55;\n"
                           "  int k;\n"
                           "  initial begin\n"
                           "    #1.55 $display(\"lit %0.2f\", $realtime);\n"
                           "    #d $display(\"param %0.2f\", $realtime);\n"
                           "    #e $display(\"realparam %0.2f\", $realtime);\n"
                           "    #r $display(\"realvar %0.2f\", $realtime);\n"
                           "    #d k = 1;\n"
                           "    #2 $display(\"int %0.2f\", $realtime);\n"
                           "  end\n"
                           "endmodule\n",
                           g),
      "lit 1.60\nparam 3.20\nrealparam 4.80\nrealvar 6.40\n"
      "int 10.00\n");
}

TEST(TimescaleSimulation, APackageClassTaskRunsInThePackagesUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ns\n"
                                 "package p;\n"
                                 "  class C;\n"
                                 "    task t(); #3; endtask\n"
                                 "  endclass\n"
                                 "endpackage\n"
                                 "`timescale 1ps / 1ps\n"
                                 "module m;\n"
                                 "  p::C c = new;\n"
                                 "  initial begin\n"
                                 "    c.t();\n"
                                 "    $display(\"%0d\", $time);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "3000\n");
}
