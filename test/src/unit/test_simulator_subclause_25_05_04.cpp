#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.5.4's example: modport A names r[3:0] P and the constant x Q, modport B
// names r[7:4] P and 2 Q, so `i.P = i.Q` through A writes 1 to the low
// nibble and through B writes 2 to the high one. Before the expression ports
// were bound, both writes were lost and r stayed all x.
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

}  // namespace
