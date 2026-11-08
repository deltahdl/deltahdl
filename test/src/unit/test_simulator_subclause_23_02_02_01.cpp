#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(NonAnsiPortExpressionSimulation, SplitPortsFillHalvesOfTheVector) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module split_ports(a[7:4], a[3:0]);\n"
                       "  input [7:0] a;\n"
                       "  initial #1 $display(\"hi %0d lo %0d a %0d\", a[7:4], "
                       "a[3:0], a);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  split_ports s(4'd10, 4'd5);\n"
                       "endmodule\n",
                       f),
            "hi 10 lo 5 a 165\n");
}

TEST(NonAnsiPortExpressionSimulation, SplitOutputPortsCarryHalvesOut) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sp(y[7:4], y[3:0]);\n"
                       "  output [7:0] y;\n"
                       "  assign y = 8'hC3;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] h, l;\n"
                       "  sp s(h, l);\n"
                       "  initial #1 $display(\"h %h l %h y %h\", h, l, s.y);\n"
                       "endmodule\n",
                       f),
            "h c l 3 y c3\n");
}

TEST(NonAnsiPortExpressionSimulation, ExplicitPortsReachConcatAndBitSelect) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module renamed_concat(.a({b, c}), f, .g(h[1]));\n"
                       "  input b, c;\n"
                       "  output [3:0] f;\n"
                       "  output [1:0] h;\n"
                       "  assign f = 4'd9;\n"
                       "  assign h = 2'b11;\n"
                       "  initial #1 $display(\"a %0d f %0d g %0d\", {b, c} + "
                       "3'd2, f, top.pg + 2'd2);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] pf;\n"
                       "  wire pg;\n"
                       "  renamed_concat r(.a(2'b11), .f(pf), .g(pg));\n"
                       "endmodule\n",
                       f),
            "a 5 f 9 g 3\n");
}

TEST(NonAnsiPortExpressionSimulation, ConcatPortAndTwoPortsOnOneInout) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module complex_ports({c, d}, .e(f));\n"
                       "  input c, d;\n"
                       "  output [3:0] f;\n"
                       "  assign f = {2'b10, c, d};\n"
                       "endmodule\n"
                       "module same_port(.a(i), .b(i));\n"
                       "  inout wire [3:0] i;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] pe, w1, w2;\n"
                       "  assign w1 = 4'h6;\n"
                       "  complex_ports cp(2'b01, pe);\n"
                       "  same_port sp(w1, w2);\n"
                       "  initial #1 $display(\"pe %b w2 %h\", pe, w2);\n"
                       "endmodule\n",
                       f),
            "pe 1001 w2 6\n");
}

}  // namespace
