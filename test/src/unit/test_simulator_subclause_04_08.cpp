#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunRace(const std::string& stimulus) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic q;\n"
      "  wire p;\n"
      "  assign p = q;\n"
      "  initial begin\n" +
          stimulus +
          "  end\n"
          "  initial #5 $display(\"settled p=%b\", p);\n"
          "endmodule\n",
      f);
}

TEST(RaceConditionSim, DisplayRacingANetUpdateShowsEitherValue) {
  std::string out = RunRace(
      "    q = 1;\n"
      "    #1 q = 0;\n"
      "    $display(\"p=%b\", p);\n");
  EXPECT_TRUE(out == "p=1\nsettled p=0\n" || out == "p=0\nsettled p=0\n")
      << out;
}

TEST(RaceConditionSim, DisplayRacingTheFirstNetUpdateShowsEitherValue) {
  std::string out = RunRace(
      "    q = 1;\n"
      "    $display(\"p=%b\", p);\n");
  EXPECT_TRUE(out == "p=z\nsettled p=1\n" || out == "p=x\nsettled p=1\n" ||
              out == "p=1\nsettled p=1\n")
      << out;
}

}  // namespace
