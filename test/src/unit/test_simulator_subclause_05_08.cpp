#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TimeLiteralSimulation, IntegerNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 10ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

TEST(TimeLiteralSimulation, FixedPointNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

TEST(TimeLiteralSimulation, ScalePs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

TEST(TimeLiteralSimulation, ScaleFs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 100fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0001);
}

TEST(TimeLiteralSimulation, ScaleUs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1000.0);
}

TEST(TimeLiteralSimulation, ScaleMs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e6);
}

TEST(TimeLiteralSimulation, ScaleS) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e9);
}

TEST(TimeLiteralSimulation, ScaledToExplicitTimeunitPs) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1ps;\n"
      "  realtime r;\n"
      "  initial r = 40ps;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 40.0);
}

// §5.8: the scaling to the current time unit applies to a fixed-point literal
// just as to an integer one. Under the default ns unit, 2.5us scales up by 1000
// to 2500.0 - exercising the fixed-point input form through a non-unit scale
// factor (the plain FixedPointNs case is ns->ns, i.e. unscaled).
TEST(TimeLiteralSimulation, FixedPointScaledToDefaultUnit) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.5us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2500.0);
}

TEST(TimeLiteralSimulation, ScaledToExplicitTimeunitUs) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  timeunit 1us;\n"
      "  realtime r;\n"
      "  initial r = 500ns;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 0.5);
}

// §5.8 scales a time literal to the current time unit, and §3.14.2.3 (printed
// page 60) makes that unit's magnitude part of it: in a 10 ns unit, 20 ns is 2
// units and 5 ns half of one. Scaled by the unit's power of ten alone, they
// read 20.0 and 5.0.
TEST(TimeLiteralSimulation, ScaledByTheMagnitudeOfTheUnit) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("module t;\n"
                           "  timeunit 10ns;\n"
                           "  timeprecision 1ns;\n"
                           "  initial $display(\"%0.1f %0.1f\", 20ns, 5ns);\n"
                           "endmodule\n",
                           f),
      "2.0 0.5\n");
}

// A module that declares no unit takes the `timescale before its header, so
// its #5ns waits 5 ns, which $realtime reads in its 1 us unit. Scaled as
// though the unit were the 1 ns default, the delay was 5 us.
TEST(TimeLiteralSimulation, ScaledToTheTimescaleBeforeTheModule) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1us/1ns\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    #5ns;\n"
                                 "    $display(\"%0.3f\", $realtime);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "0.005\n");
}

// Without a `timescale, a module that declares no unit takes the compilation
// unit's.
TEST(TimeLiteralSimulation, ScaledToTheCompilationUnitTimeunit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("timeunit 1us;\n"
                                 "module t;\n"
                                 "  initial $display(\"%0.3f\", 500ns);\n"
                                 "endmodule\n",
                                 f),
            "0.500\n");
}

// A module nested in another (§23.4) that declares no unit takes the
// enclosing one's.
TEST(TimeLiteralSimulation, ScaledToTheEnclosingModuleUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("module top;\n"
                                 "  timeunit 1us;\n"
                                 "  module inner;\n"
                                 "    initial $display(\"%0.3f\", 250ns);\n"
                                 "  endmodule\n"
                                 "  inner i();\n"
                                 "endmodule\n",
                                 f),
            "0.250\n");
}

// A package is a time scope of its own (§3.14.2.2): its function returns
// 500 ns in the 1 us unit of the `timescale before it, whatever the unit of
// the module that calls it.
TEST(TimeLiteralSimulation, ScaledToThePackageUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1us/1ns\n"
                                 "package p;\n"
                                 "  function automatic realtime f();\n"
                                 "    return 500ns;\n"
                                 "  endfunction\n"
                                 "endpackage\n"
                                 "`timescale 1ns/1ns\n"
                                 "module t;\n"
                                 "  initial $display(\"%0.3f\", p::f());\n"
                                 "endmodule\n",
                                 f),
            "0.500\n");
}

// A literal written outside every design element stands in the
// compilation-unit scope and takes its unit.
TEST(TimeLiteralSimulation, ScaledToTheUnitOfTheCompilationUnitScope) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("timeunit 1us;\n"
                                 "function automatic realtime f();\n"
                                 "  return 500ns;\n"
                                 "endfunction\n"
                                 "module t;\n"
                                 "  initial $display(\"%0.3f\", f());\n"
                                 "endmodule\n",
                                 f),
            "0.500\n");
}

// §5.7.1 lets an underscore stand between the digits of the number, and it
// adds nothing to the value: 1_500ps is 1.5 ns.
TEST(TimeLiteralSimulation, UnderscoreBetweenDigitsIsIgnored) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("module t;\n"
                                 "  initial $display(\"%0.1f\", 1_500ps);\n"
                                 "endmodule\n",
                                 f),
            "1.5\n");
}

// A parameter declared in a module's header belongs to the module, so a time
// literal in its default takes the module's unit, though the timeunit is
// declared only in the body that follows. Credited to the compilation-unit
// scope around the header, 500 ns read 500.000.
TEST(TimeLiteralSimulation, HeaderParameterDefaultTakesTheElementUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("module m #(parameter realtime P = 500ns);\n"
                                 "  timeunit 1us;\n"
                                 "  initial $display(\"%0.3f\", P);\n"
                                 "endmodule\n",
                                 f),
            "0.500\n");
}

// The same for a nested module, whose header stands inside the enclosing
// module: its literal takes the nested module's own 1 us unit, not the 1 ns
// one of the module around it.
TEST(TimeLiteralSimulation, NestedHeaderParameterTakesItsOwnElementUnit) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("module top;\n"
                           "  timeunit 1ns;\n"
                           "  module inner #(parameter realtime P = 500ns);\n"
                           "    timeunit 1us;\n"
                           "    initial $display(\"%0.3f\", P);\n"
                           "  endmodule\n"
                           "  inner i();\n"
                           "endmodule\n",
                           f),
      "0.500\n");
}

}  // namespace
