// §6.20.2 Value parameters — the runtime value a parameter carries.
//
// A parameter's value is fixed during elaboration, but whether it survives to
// run time as the type it was declared with is a property of the lowering, so
// these tests read the value back out of a running module rather than
// inspecting the elaborated parameter. A real parameter is the case that
// distinguishes the two: an integer-only representation resolves it to
// something, or fails to resolve it at all, and either way the fraction is gone
// before any process can read it.
#include "fixture_simulator.h"

using namespace delta;

namespace {

// §6.20.2: "A parameter declared with a real type" takes a real value, so a
// fractional default must read back whole. A value truncated to an integer
// would display 2, and one that failed to resolve would leave the name
// undeclared and display 0.
TEST(ValueParameterSim, RealParameterKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = 2.5;\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "2.5\n");
}

// The localparam form of the same rule. §6.20.4 makes a localparam a parameter
// that cannot be overridden, not a different kind of value, so its real-ness is
// carried the same way -- and it is the form a nested expression is most likely
// to name.
TEST(ValueParameterSim, RealLocalparamKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam real R = 0.125;\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "0.125\n");
}

// §6.20.2 covers a value parameter wherever it is written, and a parameter port
// is the other place it can be written. The two positions are elaborated by
// different code, so a real value carried in one of them says nothing about the
// other, and this is the port half.
TEST(ValueParameterSim, RealParameterPortKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter real R = 1.5);\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "1.5\n");
}

// A real parameter whose default happens to have no fraction is still a real,
// so it divides as one. Reading the default as the integer it can also be
// spelled as would make this 0 -- which is why the real fold is tried before
// the integer fold rather than after it.
TEST(ValueParameterSim, RealParameterWithoutAFractionIsStillReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = 2;\n"
                       "  initial $display(\"%g\", R / 4);\n"
                       "endmodule\n",
                       f),
            "0.5\n");
}

// The guard that carrying a real value did not disturb the integer path: an
// integer-typed parameter set from a real constant is still converted per
// §6.12.1 (round to nearest, ties away from zero), so 2.5 becomes 3.
TEST(ValueParameterSim, IntegerParameterFromRealConstantStillRounds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int N = 2.5;\n"
                       "  initial $display(\"%0d\", N);\n"
                       "endmodule\n",
                       f),
            "3\n");
}

}  // namespace
