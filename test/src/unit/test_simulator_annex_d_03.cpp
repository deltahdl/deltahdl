#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GetpatternSim, EachIndexChangeDrivesThePatternItNames) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  integer index;\n"
      "  wire i1, i2, i3;\n"
      "  assign {i1, i2, i3} = $getpattern(in_mem[index]);\n"
      "  initial begin\n"
      "    in_mem[1] = 3'b101;\n"
      "    in_mem[2] = 3'b010;\n"
      "    index = 1;\n"
      "    #1 $display(\"%b%b%b\", i1, i2, i3);\n"
      "    index = 2;\n"
      "    #1 $display(\"%b%b%b\", i1, i2, i3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "101\n010\n");
}

}  // namespace
