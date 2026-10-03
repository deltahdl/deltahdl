#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.3 with §23.3.3.5: each element of an array of interface instances is an
// instance of its own, holding its own members and carrying the parameter
// override its instantiation wrote, here shared with a scalar instance of the
// same item. `vector[3].P` is 100, `plain` and the elements of `pv`,
// instantiated with no override, keep the default 7, and a write to a member
// of an element is read back.
TEST(InterfaceInstanceArraySim, ElementsHoldMembersAndParameters) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface myif #(parameter P = 7); int x; "
                       "endinterface\n"
                       "module top;\n"
                       "  myif #(100) scalar1(), vector[3:0]();\n"
                       "  myif plain();\n"
                       "  myif pv[1:0]();\n"
                       "  initial begin\n"
                       "    vector[2].x = 12;\n"
                       "    plain.x = 3;\n"
                       "    pv[0].x = 5;\n"
                       "    $display(\"P=%0d P=%0d P=%0d x=%0d x=%0d x=%0d\", "
                       "vector[3].P, plain.P, pv[1].P, vector[2].x, plain.x, "
                       "pv[0].x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "P=100 P=7 P=7 x=12 x=3 x=5\n");
}

}  // namespace
