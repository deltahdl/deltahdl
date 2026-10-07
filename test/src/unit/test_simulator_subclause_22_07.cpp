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

// §22.7 (printed page 716): `timescale sets the time unit and time precision of
// the design elements after it, and the time unit is what time values, the
// simulation time and delays among them, are measured in. A module under
// `timescale 1us / 1ns reports that scale to $printtimescale, and its #1 is a
// microsecond, which its own $time reads as 1. Every module reported 1ns / 1ns
// whatever the directive said.
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

// §3.14.2.3 (printed page 60): a module declaring no timeunit takes "the units
// of the last `timescale directive", so two directives before two modules give
// each its own, and each module's $printtimescale with no argument reports its
// own scope's.
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

// §22.7: a delay counts the unit of the module it is written in, and $time
// reads the time in the unit of the module calling it. a's #10 is 10 ns, b's #2
// is 2 us, and a's function called 10 us in reads 10000 of a's nanoseconds. The
// two modules ran in one unit, so b's #2 fired before a's #10 and the last
// line read 10.
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

// §3.14.2.3 (printed page 60): "The time unit of the compilation-unit scope can
// only be set by a timeunit declaration, not a `timescale directive", so a task
// of a class the compilation unit declares waits its #5 in that scope's unit,
// the 1 ns default, whichever module calls it: 0.005 of the calling module's
// microseconds. The task waited 5 of the caller's units.
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

// §22.7: a gate's, a continuous assignment's and a nonblocking assignment's
// delays, and a trireg's charge decay time, are delay values like a delay
// control's, so under `timescale 1ns / 1ps a #3 is 3 ns and a #2.5 is 2.5 ns,
// kept to the picosecond precision (§3.14.1). Each was taken as that many
// ticks of the 1 ps precision, and a real one as its bit pattern.
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

// §22.7: a gate in a module under `timescale 1us / 1ns delays by its own unit
// when instantiated from a module under 1ns / 1ns, so its #2 is 2000 of the
// instantiating module's nanoseconds.
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

// §22.7 (printed page 717): under `timescale 1 ns / 1 ps delays are rounded to
// reals of three decimal places, the precision and not the unit deciding, so
// under 1ns / 100ps a #1.46 is 1.5 ns: $realtime reads 1.50 and $time, an
// integer (§20.3.1), 2. The delay was rounded to the whole unit and both read
// 1.
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

// §22.7 (printed page 717), the clause's own module: under `timescale 10 ns /
// 1 ns, parameter d's 1.55 rounds to 1.6 by the time precision, so
// `#d set = 0;` assigns at 16 ns and `#d set = 1;` at 32 ns, $realtime reading
// 1.6 and 3.2 of the 10 ns unit. Neither assignment waited at all, and a real
// literal, a real parameter and a real variable written as delay controls each
// rounded to the whole unit.
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

// §22.7 with §3.2 and §3.14.2.3: the `timescale before a package is the
// package's, so a task of a class the package declares reads its #3 in the
// package's nanoseconds, 3000 of the module's picoseconds. It was read in the
// calling module's unit, 3.
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
