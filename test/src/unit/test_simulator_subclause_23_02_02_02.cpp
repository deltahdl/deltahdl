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

TEST(ExplicitAnsiPortRun, AStructureMemberDrivesTheOutput) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(output .M(s.hi));\n"
                       "  struct packed { logic [3:0] hi, lo; } s;\n"
                       "  assign s = 8'hA5;\n"
                       "endmodule\n"
                       "module t;\n  wire [3:0] w;\n  m u(w);\n"
                       "  initial #1 $display(\"%h\", w);\nendmodule\n",
                       f),
            "a\n");
}

TEST(ExplicitAnsiPortRun, AnArrayElementCarriesAValueEachWay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(output .E(arr[1]), input .I(arr2[0]));\n"
                       "  logic [3:0] arr [2];\n"
                       "  wire [3:0] arr2 [2];\n"
                       "  assign arr[1] = 4'd6;\n"
                       "  initial #1 $display(\"in %0d\", arr2[0]);\n"
                       "endmodule\n"
                       "module t;\n  wire [3:0] w;\n  m u(w, 4'd9);\n"
                       "  initial #2 $display(\"out %0d\", w);\nendmodule\n",
                       f),
            "in 9\nout 6\n");
}

TEST(ExplicitAnsiPortRun, DISABLED_AnAssignmentPatternDrivesTheOutput) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(output .A('{x, y}));\n"
                       "  logic [3:0] x, y;\n"
                       "  assign x = 4'd1;\n"
                       "  assign y = 4'd2;\n"
                       "endmodule\n"
                       "module t;\n  wire [3:0] w [2];\n  m u(w);\n"
                       "  initial #1 $display(\"%0d %0d\", w[0], w[1]);\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

TEST(ExplicitAnsiPortRun, DISABLED_AnAssignmentPatternTakesTheInput) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input .A('{x, y}));\n"
                       "  wire [3:0] x, y;\n"
                       "  initial #1 $display(\"%0d %0d\", x, y);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic [3:0] w [2] = '{4'd3, 4'd4};\n"
                       "  m u(w);\nendmodule\n",
                       f),
            "3 4\n");
}

TEST(ExplicitAnsiPortRun, AnInterfaceHeaderCarriesSlicesEachWay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc(output .P(r[3:0]), input .Q(s[1:0]));\n"
                       "  logic [7:0] r;\n"
                       "  wire [3:0] s;\n"
                       "  assign r = 8'h5C;\n"
                       "  initial #1 $display(\"in %b\", s[1:0]);\n"
                       "endinterface\n"
                       "module t;\n  wire [3:0] p;\n  ifc u(p, 2'b10);\n"
                       "  initial #2 $display(\"out %h\", p);\nendmodule\n",
                       f),
            "in 10\nout c\n");
}

TEST(ExplicitAnsiPortRun, AProgramHeaderCarriesSlicesEachWay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program prg(output .P(r[7:4]), input .Q(s[3:2]));\n"
                       "  logic [7:0] r;\n"
                       "  wire [3:0] s;\n"
                       "  assign r = 8'hC5;\n"
                       "  initial #1 $display(\"in %b\", s[3:2]);\n"
                       "  initial #3;\n"
                       "endprogram\n"
                       "module t;\n  wire [3:0] p;\n  prg u(p, 2'b01);\n"
                       "  initial #2 $display(\"out %h\", p);\nendmodule\n",
                       f),
            "in 01\nout c\n");
}

}  // namespace
