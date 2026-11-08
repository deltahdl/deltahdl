#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PortCoercionSim, DrivenInputNetPortIsCoercedToInout) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m(input wire a);\n"
                 "  assign a = 1'b1;\n"
                 "  initial #1 $display(\"seen %0d drv %0d\", a, top.w);\n"
                 "endmodule\n"
                 "module top;\n"
                 "  wire w;\n"
                 "  m i(.a(w));\n"
                 "endmodule\n",
                 f),
      "seen 1 drv 1\n");
}

TEST(PortCoercionSim, CoercedPortDriversResolveAndVariablesStayInputs) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input wire a);\n"
                       "  assign a = 1'b1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire w;\n"
                       "  assign w = 1'b0;\n"
                       "  logic v = 0;\n"
                       "  m i(.a(w));\n"
                       "  m j(.a(v));\n"
                       "  initial #1 $display(\"w %b v %0d\", w, v);\n"
                       "endmodule\n",
                       f),
            "w x v 0\n");
}

}  // namespace
