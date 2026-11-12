#pragma once

#include <gtest/gtest.h>

#include <initializer_list>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

namespace delta {

inline std::string SampledVerdict(
    const std::string& expr, const std::string& clock = "@(posedge clk) ") {
  return "assert property (" + clock + expr +
         ") $display(\"P%0t\", $time); else $display(\"F%0t\", $time);";
}

inline std::string ProceduralVerdict(const std::string& expr) {
  return "$display(\"%s%0t\", (" + expr + ") ? \"P\" : \"F\", $time);";
}

inline std::string SampledBench(const std::string& items,
                                const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, clk2 = 0, a = 0, b = 0, en = 0;\n"
         "  logic [3:0] v = 4'd0;\n"
         "  global clocking gc @(posedge clk); endclocking\n"
         "  initial repeat (8) begin #5 clk = ~clk; clk2 = ~clk2; end\n"
         "  initial begin\n"
         "    #5 a = 1; v = 4'd9;\n"
         "    #10 a = 0; b = 1; v = 4'd2;\n"
         "    #10 a = 1; en = 1; v = 4'd12;\n"
         "    #10 a = 0; b = 0; v = 4'd3;\n"
         "  end\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

inline void ExpectOnlyPasses(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors()) << src;
  std::istringstream lines(out);
  std::string line;
  int passes = 0;
  int failures = 0;
  while (std::getline(lines, line)) {
    if (line.rfind('P', 0) == 0) ++passes;
    if (line.rfind('F', 0) == 0) ++failures;
  }
  EXPECT_GT(passes, 0) << src << out;
  EXPECT_EQ(failures, 0) << src << out;
}

inline void ExpectEachAlwaysHolds(
    std::initializer_list<const char*> exprs,
    const std::string& clock = "@(posedge clk) ") {
  for (const char* expr : exprs) {
    ExpectOnlyPasses(SampledBench(SampledVerdict(expr, clock)));
  }
}

inline std::string LinesStartingWith(const std::string& out,
                                     const std::string& prefix) {
  std::istringstream lines(out);
  std::string line;
  std::string joined;
  while (std::getline(lines, line)) {
    if (line.rfind(prefix, 0) != 0) continue;
    if (!joined.empty()) joined += ' ';
    joined += line.substr(prefix.size());
  }
  return joined;
}

inline void ExpectLines(const std::string& src, const std::string& prefix,
                        const std::string& expected) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors()) << src;
  EXPECT_EQ(LinesStartingWith(out, prefix), expected) << src << out;
}

}  // namespace delta
