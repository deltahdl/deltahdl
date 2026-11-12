#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

std::string ClockvarBench(const std::string& block, const std::string& items) {
  return "module top;\n"
         "  logic clk = 0, a = 0; int n = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) n <= n + 1;\n"
         "  initial begin #5 a = 1; #10 a = 0; #10 a = 1; end\n"
         "  clocking cb @(posedge clk);\n"
         "    " +
         block +
         "\n"
         "  endclocking\n"
         "  " +
         items +
         "\n"
         "  initial #32 $finish;\n"
         "endmodule\n";
}

void ExpectEachBlockReadsTheSample(std::initializer_list<const char*> blocks) {
  for (const char* block : blocks) {
    ExpectOnlyPasses(ClockvarBench(block, SampledVerdict("cb.a == n[0]")));
  }
}

TEST(ClockvarSamplingRun,
     DISABLED_ADefaultSkewClockvarReadDirectlyIsTheSample) {
  ExpectEachBlockReadsTheSample({"input a;"});
}

TEST(ClockvarSamplingRun, AnExplicitOneStepSkewIsTheSample) {
  ExpectEachBlockReadsTheSample({"input #1step a;",
                                 "default input #1step; input a;",
                                 "default input #2; input #1step a;"});
}

TEST(ClockvarSamplingRun, AnInputAndOutputsOneStepSkewIsTheSample) {
  ExpectEachBlockReadsTheSample({"input #1step output #1 a;"});
}

TEST(ClockvarSamplingRun, DISABLED_AnInoutsOneStepSkewIsTheSample) {
  ExpectEachBlockReadsTheSample({"inout a;", "default input #1step; inout a;"});
}

TEST(ClockvarSamplingRun, AnAssertionReadingTheSignalBesideASkewedBlockRuns) {
  for (const char* block :
       {"input #2 a;", "input #2 a;\n    property p1; a; endproperty"}) {
    ExpectOnlyPasses(ClockvarBench(block, SampledVerdict("a == n[0]")));
  }
}

}  // namespace
