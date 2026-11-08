#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& body, const std::string& print) {
  return "class Uniform;\n"
         "  rand bit [7:0] y;\n"
         "  rand real v;\n"
         "  constraint c { v > 0.0 && v < 2.0; }\n"
         "endclass\n"
         "module t;\n"
         "  int counts[256];\n"
         "  initial begin\n"
         "    static Uniform u = new;\n"
         "    static int repeats = 0, lower = 0, upper = 0, most = 0, drawn = "
         "0;\n"
         "    bit [7:0] last;\n"
         "    for (int i = 0; i < 2048; i++) begin\n"
         "      void'(u.randomize());\n" +
         body + "    end\n" + print +
         "  end\n"
         "endmodule\n";
}

TEST(RandModifierRun, AnIntegralVariableIsUniformOverItsRange) {
  SimFixture f;
  std::string out = RunCapture(
      Design("      counts[u.y]++;\n"
             "      if (i > 0 && u.y == last) repeats++;\n"
             "      last = u.y;\n",
             "    for (int k = 0; k < 256; k++) begin\n"
             "      if (counts[k] > 0) drawn++;\n"
             "      if (counts[k] > most) most = counts[k];\n"
             "    end\n"
             "    $display(\"%0d %0d %0d\", drawn >= 240, most <= 24, "
             "repeats <= 24);\n"),
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

TEST(RandModifierRun, ARealVariableIsUniformOverItsRange) {
  SimFixture f;
  std::string out = RunCapture(
      Design("      if (u.v < 1.0) lower++; else upper++;\n"
             "      if (u.v > 0.0 && u.v < 2.0) drawn++;\n",
             "    $display(\"%0d %0d\", (lower > upper ? lower - upper : "
             "upper - lower) <= 341, drawn == 2048);\n"),
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
