#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

TEST(TimeFunctionSim, AllThreeReportCurrentTime) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #5;\n"
      "    if ($time == 5) $display(\"time_ok\");\n"
      "    if ($stime == 5) $display(\"stime_ok\");\n"
      "    if ($realtime == 5.0) $display(\"realtime_ok\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "time_ok\nstime_ok\nrealtime_ok\n");
}

TEST(TimeFunctionSim, TimeTracksAdvancingScheduler) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #3;\n"
      "    if ($time == 3) $display(\"t3\");\n"
      "    #4;\n"
      "    if ($time == 7) $display(\"t7\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t3\nt7\n");
}

TEST(TimeFunctionSim, RealtimeTracksAdvancingScheduler) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #2;\n"
      "    if ($realtime == 2.0) $display(\"r2\");\n"
      "    #6;\n"
      "    if ($realtime == 8.0) $display(\"r8\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "r2\nr8\n");
}

TEST(TimeFunctionSim, StimeTracksAdvancingScheduler) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    #4;\n"
      "    if ($stime == 4) $display(\"s4\");\n"
      "    #5;\n"
      "    if ($stime == 9) $display(\"s9\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s4\ns9\n");
}

TEST(TimeFunctionSim, AllThreeReportZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    if ($time == 0) $display(\"time0\");\n"
      "    if ($stime == 0) $display(\"stime0\");\n"
      "    if ($realtime == 0.0) $display(\"realtime0\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "time0\nstime0\nrealtime0\n");
}

struct TimeFunction {
  const char* name;
  const char* format;
};

constexpr TimeFunction kTimeFunctions[] = {
    {"$time", "%0d"}, {"$stime", "%0d"}, {"$realtime", "%0.2f"}};

std::string Show(const TimeFunction& fn) {
  return std::string("$display(\"") + fn.format + "\", " + fn.name + ");";
}

std::string RunSource(const std::string& src) {
  SimFixture f;
  return PreprocessAndCapture(src, f);
}

void ExpectEach(std::string (*source)(const TimeFunction&),
                const char* const (&expected)[3]) {
  for (int i = 0; i < 3; ++i) {
    EXPECT_EQ(RunSource(source(kTimeFunctions[i])),
              std::string(expected[i]) + "\n")
        << kTimeFunctions[i].name;
  }
}

constexpr const char* kInNanoseconds[3] = {"1600", "1600", "1600.00"};
constexpr const char* kInMicroseconds[3] = {"2", "2", "1.60"};

std::string NestedModule(const TimeFunction& fn) {
  return "`timescale 1us / 1ps\n"
         "module top;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ps;\n"
         "  module inner;\n"
         "    initial begin #1600ns; " +
         Show(fn) +
         " end\n"
         "  endmodule\n"
         "  inner u();\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, ANestedModuleReadsTheEnclosingModulesUnit) {
  ExpectEach(NestedModule, kInNanoseconds);
}

std::string Interface(const TimeFunction& fn) {
  return "interface i;\n"
         "  timeunit 1us;\n"
         "  timeprecision 1ns;\n"
         "  initial begin #1600ns; " +
         Show(fn) +
         " end\n"
         "endinterface\n"
         "module top;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ns;\n"
         "  i u();\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, AnInterfaceReadsItsOwnUnit) {
  ExpectEach(Interface, kInMicroseconds);
}

std::string PackageFunction(const TimeFunction& fn) {
  return "package p;\n"
         "  timeunit 1us;\n"
         "  timeprecision 1ns;\n"
         "  function void show(); " +
         Show(fn) +
         " endfunction\n"
         "endpackage\n"
         "module t;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ns;\n"
         "  initial #1600 p::show();\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, APackageFunctionReadsThePackagesUnit) {
  ExpectEach(PackageFunction, kInMicroseconds);
}

std::string PackageClassMethod(const TimeFunction& fn) {
  return "package p;\n"
         "  timeunit 1us;\n"
         "  timeprecision 1ns;\n"
         "  class C;\n"
         "    static function void show(); " +
         Show(fn) +
         " endfunction\n"
         "  endclass\n"
         "endpackage\n"
         "module t;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ns;\n"
         "  initial #1600 p::C::show();\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, AClassMethodReadsItsPackagesUnit) {
  ExpectEach(PackageClassMethod, kInMicroseconds);
}

std::string Program(const TimeFunction& fn) {
  return "program pr;\n"
         "  timeunit 1us;\n"
         "  timeprecision 1ns;\n"
         "  initial begin #1600ns; " +
         Show(fn) +
         " end\n"
         "endprogram\n"
         "module top;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ns;\n"
         "  pr u();\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, AProgramReadsItsOwnUnit) {
  ExpectEach(Program, kInMicroseconds);
}

std::string CompilationUnitTimeunit(const TimeFunction& fn) {
  return "timeunit 1us;\n"
         "timeprecision 1ns;\n"
         "module t;\n"
         "  initial begin #1600ns; " +
         Show(fn) +
         " end\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, AModuleReadsTheCompilationUnitsTimeunit) {
  ExpectEach(CompilationUnitTimeunit, kInMicroseconds);
}

std::string TimescaleDirective(const TimeFunction& fn) {
  return "`timescale 1us / 1ns\n"
         "module t;\n"
         "  initial begin #1.6; " +
         Show(fn) +
         " end\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, AModuleReadsTheTimescaleDirectivesUnit) {
  ExpectEach(TimescaleDirective, kInMicroseconds);
}

std::string HierarchicalCall(const TimeFunction& fn) {
  return "module m1;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ns;\n"
         "  function void show(); " +
         Show(fn) +
         " endfunction\n"
         "endmodule\n"
         "module m2;\n"
         "  timeunit 1us;\n"
         "  timeprecision 1ns;\n"
         "  initial #1.6 top.a.show();\n"
         "endmodule\n"
         "module top;\n"
         "  timeunit 1ns;\n"
         "  timeprecision 1ns;\n"
         "  m1 a();\n"
         "  m2 b();\n"
         "endmodule\n";
}

TEST(TimeFunctionScope, AFunctionReadsTheUnitOfTheModuleDeclaringIt) {
  ExpectEach(HierarchicalCall, kInNanoseconds);
}

TEST(TimeFunctionResult, WidthSignAndRealnessInAnExpression) {
  EXPECT_EQ(
      RunSource("module t;\n"
                "  timeunit 10ns;\n"
                "  timeprecision 1ns;\n"
                "  initial begin\n"
                "    $display(\"%0d %0d %0d\", $bits($time), $bits($stime),\n"
                "      $time - 1 > 0);\n"
                "    #1.6 $display(\"%0.2f\", $realtime / 2);\n"
                "  end\n"
                "endmodule\n"),
      "64 32 1\n0.80\n");
}

}  // namespace
