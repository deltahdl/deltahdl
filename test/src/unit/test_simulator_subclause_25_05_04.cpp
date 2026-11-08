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

}  // namespace
