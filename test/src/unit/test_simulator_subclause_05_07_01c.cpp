#include <gtest/gtest.h>

#include <format>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(IntegerLiteralSim, TrailingUnderscoreIsIgnored) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 12_;\n"
                      "endmodule\n",
                      "x"),
            12u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 8'hF_;\n"
                      "endmodule\n",
                      "x"),
            15u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 4'b10_;\n"
                      "endmodule\n",
                      "x"),
            2u);
}

TEST(IntegerLiteralSim, DoubledUnderscoresAreIgnored) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 1__2;\n"
                      "endmodule\n",
                      "x"),
            12u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 8'b1__0;\n"
                      "endmodule\n",
                      "x"),
            2u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 'h1___F;\n"
                      "endmodule\n",
                      "x"),
            31u);
}

TEST(IntegerLiteralSim, UnderscoreInTheSizeLeavesTheSize) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int x;\n"
                      "  initial x = $bits(1_6'h12);\n"
                      "endmodule\n",
                      "x"),
            16u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial x = 1_6'h3_FFFF;\n"
                      "endmodule\n",
                      "x"),
            0xFFFFu);
}

TEST(IntegerLiteralSim, UnderscoresInARealOrTimeLiteralAreIgnored) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  real r;\n"
                                 "  initial r = 1__0_.2__5_;\n"
                                 "endmodule\n",
                                 "r"),
                   10.25);
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  real r;\n"
                                 "  initial r = 2_5e0__1_;\n"
                                 "endmodule\n",
                                 "r"),
                   250.0);
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  realtime r;\n"
                                 "  initial r = 1__0_ns;\n"
                                 "endmodule\n",
                                 "r"),
                   10.0);
}

struct UnbasedUnsizedForm {
  const char* literal;
  const char* bits;
};

std::string UnbasedUnsizedDesign(const char* literal) {
  std::string src =
      "module s(input logic [3:0] i, output logic [3:0] o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module t;\n"
      "  parameter logic [3:0] P = ";
  src += literal;
  src += ";\n  logic [3:0] a;\n  wire [3:0] b;\n  s u(.i(";
  src += literal;
  src += "), .o(b));\n  initial begin\n    a = ";
  src += literal;
  src += ";\n    #1 $display(\"%b %b %b\", a, P, b);\n  end\nendmodule\n";
  return src;
}

TEST(IntegerLiteralSim, EachUnbasedUnsizedFormFillsItsTarget) {
  for (const UnbasedUnsizedForm& c :
       {UnbasedUnsizedForm{"'0", "0000"}, UnbasedUnsizedForm{"'1", "1111"},
        UnbasedUnsizedForm{"'x", "xxxx"}, UnbasedUnsizedForm{"'X", "xxxx"},
        UnbasedUnsizedForm{"'z", "zzzz"}, UnbasedUnsizedForm{"'Z", "zzzz"}}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(UnbasedUnsizedDesign(c.literal), f),
              std::format("{0} {0} {0}\n", c.bits))
        << c.literal;
  }
}

}  // namespace
