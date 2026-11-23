#include <gtest/gtest.h>

#include <string>

#include "fixture_scratch_dir.h"
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

std::string SteppedPatterns(const std::string& fill) {
  std::string src =
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  integer i;\n"
      "  wire a, b, c;\n"
      "  assign {a, b, c} = $getpattern(m[i]);\n"
      "  initial begin\n";
  src += fill;
  src +=
      "    i = 1;\n"
      "    #1 $display(\"%b%b%b\", a, b, c);\n"
      "    i = 2;\n"
      "    #1 $display(\"%b%b%b\", a, b, c);\n"
      "  end\n"
      "endmodule\n";
  return src;
}

TEST(GetpatternSim, TheLeftmostNetTakesTheLeftmostBitOfTheWord) {
  SimFixture f;
  EXPECT_EQ(RunCapture(SteppedPatterns("    m[1] = 3'b100;\n"
                                       "    m[2] = 3'b011;\n"),
                       f),
            "100\n011\n");
}

TEST(GetpatternSim, PatternsLoadedByReadmembAreDriven) {
  ScratchDir tmp;
  auto path = tmp.Write("patt.mem", "011\n100\n");
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          SteppedPatterns("    $readmemb(\"" + path.string() + "\", m);\n"), f),
      "011\n100\n");
}

TEST(GetpatternSim, PatternsLoadedByReadmemhAreDriven) {
  ScratchDir tmp;
  auto path = tmp.Write("patt.mem", "3\n4\n");
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          SteppedPatterns("    $readmemh(\"" + path.string() + "\", m);\n"), f),
      "011\n100\n");
}

TEST(GetpatternSim, DISABLED_RewritingTheWordAtAFixedIndexDrivesItAgain) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic [1:3] m [1:2];\n"
                       "  integer i;\n"
                       "  wire a, b, c;\n"
                       "  assign {a, b, c} = $getpattern(m[i]);\n"
                       "  initial begin\n"
                       "    m[1] = 3'b100;\n"
                       "    i = 1;\n"
                       "    #1 $display(\"%b%b%b\", a, b, c);\n"
                       "    m[1] = 3'b110;\n"
                       "    #1 $display(\"%b%b%b\", a, b, c);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "100\n110\n");
}

}  // namespace
