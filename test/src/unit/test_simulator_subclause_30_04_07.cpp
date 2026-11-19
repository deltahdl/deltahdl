#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string PolarityRun(const std::string& gate, const std::string& path) {
  SimFixture f;
  return RunCapture("module leaf(input a, output y);\n  " + gate +
                        " (y, a);\n  specify\n    (" + path +
                        ") = (3, 7);\n  endspecify\nendmodule\n"
                        "module top;\n  logic a; wire y;\n"
                        "  leaf u(.a(a), .y(y));\n"
                        "  always @(y) if ($time >= 10)\n"
                        "    $display(\"t=%0t y=%b\", $time, y);\n"
                        "  initial begin a = 0; #20 a = 1; #20 a = 0; end\n"
                        "endmodule\n",
                    f);
}

constexpr char kBufferTiming[] = "t=23 y=1\nt=47 y=0\n";
constexpr char kInverterTiming[] = "t=27 y=0\nt=43 y=1\n";

TEST(ModulePathPolarityRun, UnknownParallelOverBufferTakesRiseThenFall) {
  EXPECT_EQ(PolarityRun("buf", "a => y"), kBufferTiming);
}

TEST(ModulePathPolarityRun, PositiveParallelOverBufferMatchesUnknown) {
  EXPECT_EQ(PolarityRun("buf", "a +=> y"), kBufferTiming);
}

TEST(ModulePathPolarityRun, NegativeParallelOverBufferKeepsRiseAndFall) {
  EXPECT_EQ(PolarityRun("buf", "a -=> y"), kBufferTiming);
}

TEST(ModulePathPolarityRun, NegativeFullOverBufferKeepsRiseAndFall) {
  EXPECT_EQ(PolarityRun("buf", "a -*> y"), kBufferTiming);
}

TEST(ModulePathPolarityRun, UnknownFullOverInverterTakesOutputTransition) {
  EXPECT_EQ(PolarityRun("not", "a *> y"), kInverterTiming);
}

TEST(ModulePathPolarityRun, PositiveParallelOverInverterTakesOutputTransition) {
  EXPECT_EQ(PolarityRun("not", "a +=> y"), kInverterTiming);
}

TEST(ModulePathPolarityRun, PositiveFullOverInverterTakesOutputTransition) {
  EXPECT_EQ(PolarityRun("not", "a +*> y"), kInverterTiming);
}

TEST(ModulePathPolarityRun, NegativeParallelOverInverterMatchesUnknown) {
  EXPECT_EQ(PolarityRun("not", "a -=> y"), kInverterTiming);
}

}  // namespace
