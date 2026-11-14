#pragma once

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

inline std::string DisableIffDesign(const std::string& modules,
                                    const std::string& instances) {
  return modules +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 1, b = 0, rst = 0, rst1 = 0;\n"
         "  always #5 clk = ~clk;\n" +
         instances +
         "  initial begin\n"
         "    #12 rst = 1;\n"
         "    #6 rst = 0;\n"
         "    #14 rst1 = 1;\n"
         "    #6 rst1 = 0;\n"
         "    #2 $finish;\n"
         "  end\n"
         "endmodule\n";
}

inline std::string RunDisableIffDesign(const std::string& modules,
                                       const std::string& instances) {
  SimFixture f;
  return RunCapture(DisableIffDesign(modules, instances), f);
}

inline std::string FailingAt(const std::string& label,
                             const std::string& indent = "  ") {
  return indent + label + ": assert property (@(posedge clk) a |=> b) else " +
         "$display(\"" + label + " at %0d\", $time);\n";
}

inline std::string ReportTimes(const std::string& out,
                               const std::string& label) {
  std::string times;
  std::string head = label + " at ";
  size_t start = 0;
  while (start < out.size()) {
    size_t end = out.find('\n', start);
    if (end == std::string::npos) end = out.size();
    if (out.compare(start, head.size(), head) == 0) {
      if (!times.empty()) times += ' ';
      times.append(out, start + head.size(), end - start - head.size());
    }
    start = end + 1;
  }
  return times;
}
