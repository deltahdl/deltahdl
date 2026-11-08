#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(EventControlSim, AnUnpackedArrayElementWakesItsEventControl) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic c[2];\n"
                       "  int k = 0, w = 0, j = 1;\n"
                       "  always @(posedge c[0]) k++;\n"
                       "  always @(c[j]) w++;\n"
                       "  initial begin\n"
                       "    c[0] = 0; c[1] = 0;\n"
                       "    forever #5 begin c[0] = ~c[0]; c[1] = ~c[1]; end\n"
                       "  end\n"
                       "  initial #41 $display(\"%0d %0d\", k, w);\n"
                       "  initial #45 $finish;\n"
                       "endmodule\n",
                       f),
            "4 9\n$finish at time 45\n");
}

TEST(EventControlSim, AnArrayPortElementWakesTheInstancesEventControl) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module p(input logic c[2]);\n"
                       "  int k = 0;\n"
                       "  always @(posedge c[0]) k++;\n"
                       "  initial #41 $display(\"k=%0d\", k);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic cs[2] = '{0, 0};\n"
                       "  always #5 cs[0] = ~cs[0];\n"
                       "  p u(cs);\n"
                       "  initial #45 $finish;\n"
                       "endmodule\n",
                       f),
            "k=4\n$finish at time 45\n");
}

}  // namespace
