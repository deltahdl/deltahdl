#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AnsiExplicitlyNamedPortSimulation, PortsCarryTheirPortExpressions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mymod(output .P1(r[3:0]), output .P2(r[7:4]), "
                       "ref .Y(x), input R);\n"
                       "  logic [7:0] r = 8'hA5;\n"
                       "  int x;\n"
                       "  initial #1 x = 77;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] p1, p2;\n"
                       "  int y;\n"
                       "  mymod m(.P1(p1), .P2(p2), .Y(y), .R(1'b1));\n"
                       "  initial #2 $display(\"P1 %0d P2 %0d Y %0d R %0d\", "
                       "p1, p2, y, m.R);\n"
                       "endmodule\n",
                       f),
            "P1 5 P2 10 Y 77 R 1\n");
}

TEST(AnsiExplicitlyNamedPortSimulation, InputReachesItsExpressionAndConcat) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input .Q(s[3:0]), output .C({a, b}));\n"
                       "  logic [7:0] s;\n"
                       "  logic [1:0] a = 2'b10;\n"
                       "  logic b = 1'b1;\n"
                       "  initial #1 $display(\"s %b\", s[3:0]);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [3:0] q = 4'hA;\n"
                       "  wire [2:0] c;\n"
                       "  m u(.Q(q), .C(c));\n"
                       "  initial #2 $display(\"c %b\", c);\n"
                       "endmodule\n",
                       f),
            "s 1010\nc 101\n");
}

}  // namespace
