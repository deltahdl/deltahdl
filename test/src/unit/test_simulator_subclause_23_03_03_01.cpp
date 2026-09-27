#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §23.3.3.1 (printed page 747): "A port that is declared as input (output)
// but used as an output (input) or inout may be coerced to inout." An input
// net port the module drives is coerced, so the port and the parent's net are
// one net and the module's `assign a = 1'b1` reaches `top.w`. The port was
// warned about and left an input, the parent's w reading z.
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

// Coerced, the module's driver is one more driver of the parent's net and
// resolves against the parent's own, a 0 and a 1 reading x. A variable
// connection is not coerced -- §23.3.3.3 lets an inout connect to a net and
// never to a variable -- so the parent's variable keeps its own value.
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
