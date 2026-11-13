#pragma once

#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_sampling_bench.h"

namespace delta {

inline std::vector<std::string> TicksOf(const std::string& spec) {
  std::vector<std::string> ticks;
  std::istringstream words(spec);
  std::string word;
  while (words >> word) ticks.push_back(word == "-" ? "" : word);
  return ticks;
}

inline std::string TickDrive(const std::vector<std::string>& ticks) {
  std::string drive;
  for (const std::string& high : ticks) {
    drive += "    #10";
    for (const char* name : {"x", "a", "b", "c"}) {
      drive += std::string(" ") + name + " = " +
               (high.find(name) != std::string::npos ? "1" : "0") + ";";
    }
    drive += "\n";
  }
  return drive + "    #10 x = 0; a = 0; b = 0; c = 0;\n";
}

inline std::string TickBench(const std::string& outside,
                             const std::string& items,
                             const std::vector<std::string>& ticks) {
  return outside +
         "module m;\n"
         "  logic clk = 0, x = 0, a = 0, b = 0, c = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  " +
         items +
         "\n"
         "  initial begin\n" +
         TickDrive(ticks) +
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

inline std::string TickLines(const std::string& outside,
                             const std::string& items,
                             const std::vector<std::string>& ticks,
                             const std::string& prefix) {
  SimFixture f;
  return LinesStartingWith(RunCapture(TickBench(outside, items, ticks), f),
                           prefix);
}

}  // namespace delta
