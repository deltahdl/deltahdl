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

TEST(TimeLiteralSimulation, ScaledToTheCompilationUnitTimeunit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("timeunit 1us;\n"
                                 "module t;\n"
                                 "  initial $display(\"%0.3f\", 500ns);\n"
                                 "endmodule\n",
                                 f),
            "0.500\n");
}

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

TEST(TimeLiteralSimulation, UnderscoreBetweenDigitsIsIgnored) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("module t;\n"
                                 "  initial $display(\"%0.1f\", 1_500ps);\n"
                                 "endmodule\n",
                                 f),
            "1.5\n");
}

TEST(TimeLiteralSimulation, HeaderParameterDefaultTakesTheElementUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("module m #(parameter realtime P = 500ns);\n"
                                 "  timeunit 1us;\n"
                                 "  initial $display(\"%0.3f\", P);\n"
                                 "endmodule\n",
                                 f),
            "0.500\n");
}

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

TEST(TimeLiteralSimulation, ScaledToTheInterfaceUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("interface i;\n"
                                 "  timeunit 1us;\n"
                                 "  initial $display(\"%0.3f\", 250ns);\n"
                                 "endinterface\n"
                                 "module t;\n"
                                 "  timeunit 1ns;\n"
                                 "  i u();\n"
                                 "endmodule\n",
                                 f),
            "0.250\n");
}

TEST(TimeLiteralSimulation, ScaledToTheProgramUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("program p;\n"
                                 "  timeunit 1us;\n"
                                 "  initial $display(\"%0.3f\", 250ns);\n"
                                 "endprogram\n"
                                 "module t;\n"
                                 "  timeunit 1ns;\n"
                                 "  p u();\n"
                                 "endmodule\n",
                                 f),
            "0.250\n");
}

TEST(TimeLiteralSimulation, ScaledToTheNestedModulesOwnUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("module top;\n"
                                 "  timeunit 1ns;\n"
                                 "  module inner;\n"
                                 "    timeunit 1us;\n"
                                 "    initial $display(\"%0.3f\", 250ns);\n"
                                 "  endmodule\n"
                                 "  inner i();\n"
                                 "endmodule\n",
                                 f),
            "0.250\n");
}

TEST(TimeLiteralSimulation, ClassMethodScaledToItsPackageUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("package p;\n"
                                 "  timeunit 1us;\n"
                                 "  class c;\n"
                                 "    static function realtime f();\n"
                                 "      return 250ns;\n"
                                 "    endfunction\n"
                                 "  endclass\n"
                                 "endpackage\n"
                                 "module t;\n"
                                 "  timeunit 1ns;\n"
                                 "  initial $display(\"%0.3f\", p::c::f());\n"
                                 "endmodule\n",
                                 f),
            "0.250\n");
}

TEST(TimeLiteralSimulation, CheckerScaledToTheScopeItIsDeclaredIn) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("timeunit 1us;\n"
                                 "checker chk;\n"
                                 "  realtime r;\n"
                                 "  assign r = 250ns;\n"
                                 "endchecker\n"
                                 "module t;\n"
                                 "  timeunit 1ns;\n"
                                 "  chk u();\n"
                                 "endmodule\n",
                                 "u.r"),
                   0.25);
  EXPECT_DOUBLE_EQ(RunAndGetReal("timeunit 1ns;\n"
                                 "module t;\n"
                                 "  timeunit 1us;\n"
                                 "  checker chk;\n"
                                 "    realtime r;\n"
                                 "    assign r = 250ns;\n"
                                 "  endchecker\n"
                                 "  chk u();\n"
                                 "endmodule\n",
                                 "u.r"),
                   0.25);
}

}  // namespace
