#include <gtest/gtest.h>

#include <format>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §5.7.1 has an underscore after a number's first character ignored, so a
// number ending in one reads as the same number without it, sized or not and
// whatever its base.
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

// Two or more underscores in a row are ignored as one is.
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

// The size is a number too, so an underscore in it is ignored and the size it
// gives takes effect: sixteen bits, which keep the low sixteen of a wider
// value.
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

// The same holds in each digit run of a real literal, which §5.7.2's syntax
// builds from the same unsigned number, and of a time literal (§5.8).
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

// One unbased unsized literal and the bits §5.7.1 has it set in a four-bit
// target, printed by %b.
struct UnbasedUnsizedForm {
  const char* literal;
  const char* bits;
};

// The design that writes `literal` as a four-bit variable's operand, as a
// parameter's value and as an input port's connection, and prints all three
// with %b once the port's value has reached the net it drives.
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

// Each of the six forms, written against its apostrophe, sets every bit of its
// target to its own bit value: as an operand, as a parameter's value and as a
// port's connection.
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
