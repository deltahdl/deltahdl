#pragma once

#include <string>

#include "fixture_simulator.h"

using namespace delta;

inline std::string ClockResolutionDesign(
    const std::string& modules,
    const std::string& instances = "  m u1(a, b, clk);\n") {
  return modules +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0, b = 0;\n"
         "  always #5 clk = ~clk;\n" +
         instances +
         "  initial begin\n"
         "    #12 a = 1;\n"
         "    #10 a = 0; b = 1;\n"
         "    #12 b = 0;\n"
         "    #6 $finish;\n"
         "  end\n"
         "endmodule\n";
}

inline std::string RunClockResolutionDesign(
    const std::string& modules,
    const std::string& instances = "  m u1(a, b, clk);\n") {
  SimFixture f;
  return RunCapture(ClockResolutionDesign(modules, instances), f);
}
