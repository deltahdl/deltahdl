#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ModportExpressionSim, WritesAndReadsThroughTheExpression) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I;\n"
                       "  logic [7:0] r;\n"
                       "  const int x = 1;\n"
                       "  modport A(output .P(r[3:0]), input .Q(x));\n"
                       "  modport B(output .P(r[7:4]), input .Q(2));\n"
                       "endinterface\n"
                       "module MA(I.A i);\n"
                       "  initial i.P = i.Q;\n"
                       "endmodule\n"
                       "module MB(I.B i);\n"
                       "  initial i.P = i.Q;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  I i1();\n"
                       "  MA u1(i1.A);\n"
                       "  MB u2(i1.B);\n"
                       "  initial #1 $display(\"r=%b\", i1.r);\n"
                       "endmodule\n",
                       f),
            "r=00100001\n");
}

TEST(ModportExpressionSim, NonblockingWriteReachesTheExpression) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I;\n"
                       "  logic [7:0] r = 8'h10;\n"
                       "  modport A(output .P(r[3:0]));\n"
                       "endinterface\n"
                       "module MA(I.A i);\n"
                       "  initial i.P <= 4'd5;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  I i1();\n"
                       "  MA u1(i1.A);\n"
                       "  initial begin\n"
                       "    #0 $display(\"before=%0d\", i1.r);\n"
                       "    #1 $display(\"after=%0d\", i1.r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "before=16\nafter=21\n");
}

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(ModportExpressionSim, WritesReachAnElementAConcatenationAndAMember) {
  EXPECT_EQ(RunWithoutErrors(
                "interface I;\n"
                "  logic m [0:2];\n"
                "  logic a, b;\n"
                "  struct packed { logic x; logic y; } s;\n"
                "  modport A(output .E(m[1]), output .C({a, b}), "
                "output .S(s.x));\n"
                "endinterface\n"
                "module M(I.A i);\n"
                "  initial begin i.E = 1; i.C = 2'b10; i.S = 1; end\n"
                "endmodule\n"
                "module top;\n"
                "  I i1();\n"
                "  initial begin i1.m[0] = 0; i1.m[2] = 0; i1.s.y = 0; end\n"
                "  M u(i1.A);\n"
                "  initial #1 $display(\"%b%b%b %b%b %b%b\", i1.m[0], "
                "i1.m[1], i1.m[2], i1.a, i1.b, i1.s.x, i1.s.y);\n"
                "endmodule\n"),
            "010 10 10\n");
}

TEST(ModportExpressionSim, APortTakesTheWidthOfItsSelectAndConcatenation) {
  EXPECT_EQ(RunWithoutErrors("interface I;\n"
                             "  logic a, b;\n"
                             "  logic [7:0] r;\n"
                             "  modport A(input .P(r[3:0]), input .C({a, b, "
                             "r}));\n"
                             "endinterface\n"
                             "module M(I.A i);\n"
                             "  initial $display(\"%0d %0d\", $bits(i.P), "
                             "$bits(i.C));\n"
                             "endmodule\n"
                             "module top;\n"
                             "  I i1();\n"
                             "  M u(i1.A);\n"
                             "endmodule\n"),
            "4 10\n");
}

TEST(ModportExpressionSim, APortTakesTheTypeOfAnIntMember) {
  EXPECT_EQ(RunWithoutErrors("interface I;\n"
                             "  struct { int k; byte c; } s;\n"
                             "  modport A(input .K(s.k));\n"
                             "endinterface\n"
                             "module M(I.A i);\n"
                             "  initial #1 $display(\"%0d %0d %0d\", "
                             "$bits(i.K), i.K, i.K < 0);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  I i1();\n"
                             "  initial i1.s.k = -7;\n"
                             "  M u(i1.A);\n"
                             "endmodule\n"),
            "32 -7 1\n");
}

TEST(ModportExpressionSim, APortTakesTheSignedTypeOfAPackedMember) {
  EXPECT_EQ(
      RunWithoutErrors("interface I;\n"
                       "  struct packed { logic signed [3:0] m; logic [7:0] "
                       "n; } s;\n"
                       "  modport A(input .S(s.m));\n"
                       "endinterface\n"
                       "module M(I.A i);\n"
                       "  initial #1 $display(\"%0d %0d %0d\", $bits(i.S), "
                       "i.S, i.S < 0);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  I i1();\n"
                       "  initial begin i1.s.m = -3; i1.s.n = 8'hFF; end\n"
                       "  M u(i1.A);\n"
                       "endmodule\n"),
      "4 -3 1\n");
}

TEST(ModportExpressionSim, DISABLED_APortTakesTheStructureTypeOfAMember) {
  EXPECT_EQ(RunWithoutErrors("package pk;\n"
                             "  typedef struct packed { logic [3:0] x; logic "
                             "[3:0] y; } pair_t;\n"
                             "endpackage\n"
                             "interface I;\n"
                             "  struct { pk::pair_t p; int k; } s;\n"
                             "  modport A(input .S(s.p));\n"
                             "endinterface\n"
                             "module M(I.A i);\n"
                             "  initial #1 $display(\"%0d %h %h\", $bits(i.S), "
                             "i.S.x, i.S.y);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  I i1();\n"
                             "  initial i1.s.p = 8'h3C;\n"
                             "  M u(i1.A);\n"
                             "endmodule\n"),
            "8 3 c\n");
}

TEST(ModportExpressionSim, ASelectPortIsNotWidenedToItsVariable) {
  EXPECT_EQ(RunWithoutErrors("interface I;\n"
                             "  logic [7:0] r = 8'hAB;\n"
                             "  modport A(output .P(r[3:0]));\n"
                             "endinterface\n"
                             "module M(I.A i);\n"
                             "  initial begin\n"
                             "    $display(\"%0d\", i.P);\n"
                             "    i.P = 8'h5C;\n"
                             "    #1 $display(\"%h\", top.i1.r);\n"
                             "  end\n"
                             "endmodule\n"
                             "module top;\n"
                             "  I i1();\n"
                             "  M u(i1.A);\n"
                             "endmodule\n"),
            "11\nac\n");
}

TEST(ModportExpressionSim, AnInputOperatorResultIsReadThroughThePort) {
  EXPECT_EQ(RunWithoutErrors("interface I;\n"
                             "  logic [1:0] a, b;\n"
                             "  modport mp(input .P(a + b));\n"
                             "endinterface\n"
                             "module M(I.mp i);\n"
                             "  initial #1 $display(\"%0d\", i.P);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  I i1();\n"
                             "  initial begin i1.a = 1; i1.b = 2; end\n"
                             "  M u(i1.mp);\n"
                             "endmodule\n"),
            "3\n");
}

TEST(ModportExpressionSim, ATypedAssignmentPatternIsReadThroughThePort) {
  EXPECT_EQ(RunWithoutErrors("interface I;\n"
                             "  typedef logic [1:0] pair_t;\n"
                             "  logic a, b;\n"
                             "  modport A(input .P(pair_t'{a, b}));\n"
                             "endinterface\n"
                             "module M(I.A i);\n"
                             "  initial #1 $display(\"%b\", i.P);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  I i1();\n"
                             "  initial begin i1.a = 1; i1.b = 0; end\n"
                             "  M u(i1.A);\n"
                             "endmodule\n"),
            "10\n");
}

}  // namespace
