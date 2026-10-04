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

// §25.5.4: a nonblocking assignment is as much a write of a modport
// expression port as a blocking one, so `i.P <= 4'd5` through modport A
// updates r[3:0] and leaves the high nibble at 1. The update lands in the NBA
// region, so a read of r in the same time step still sees 16. Before the
// target was routed through the expression, the write was lost and r stayed
// 16.
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

}  // namespace
