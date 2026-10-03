#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

TEST(DefaultNettypeSimulation, WireModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`default_nettype wire\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result", CuPropagation::kDefaultNetType);
  EXPECT_EQ(result, 42u);
}

// A module p0 passing its input i to its output o.
static const std::string kPassThrough =
    "module p0(input logic i, output logic o);\n"
    "  assign o = i;\n"
    "endmodule\n";

// §22.8: `default_nettype governs the module definitions that follow it, so a
// directive after the last module reaches back to none of them: t's implicit
// nets und and w are tri1, und pulling p0's input to 1. The trailing
// `default_nettype wire governed every module, and w read z.
TEST(DefaultNettypeSimulation, ATrailingDirectiveLeavesTheModulesBeforeIt) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`default_nettype tri1\n" + kPassThrough +
                                     "module t;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "  initial #1 $display(\"%b\", w);\n"
                                     "endmodule\n"
                                     "`default_nettype wire\n",
                                 f),
            "1\n");
}

// §22.8: `default_nettype wire in force at t gives t's undeclared und and w
// implicit wires, which a `none` before p0 or after t does not forbid; und is
// undriven, so w reads z. The trailing none governed t, and und and w were
// reported as implicit nets it forbids.
TEST(DefaultNettypeSimulation, NoneBeforeAndAfterLeavesAWireModuleItsNets) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`default_nettype none\n" + kPassThrough +
                                     "`default_nettype wire\n"
                                     "module t;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "  initial #1 $display(\"%b\", w);\n"
                                     "endmodule\n"
                                     "`default_nettype none\n",
                                 f),
            "z\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

// §22.8: each of t0, t1 and t2 takes the `default_nettype before it, so its
// implicit und is a tri0 reading 0, a tri1 reading 1 and an undriven wire
// reading z, and each passes the value through p0 to its w. The last
// directive, wire, governed all three, which read z z z.
TEST(DefaultNettypeSimulation, EachModuleTakesTheDirectiveBeforeIt) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`default_nettype tri0\n" + kPassThrough +
                                     "module t0;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "endmodule\n"
                                     "`default_nettype tri1\n"
                                     "module t1;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "endmodule\n"
                                     "`default_nettype wire\n"
                                     "module t2;\n"
                                     "  p0 u(.i(und), .o(w));\n"
                                     "endmodule\n"
                                     "module t;\n"
                                     "  t0 a();\n"
                                     "  t1 b();\n"
                                     "  t2 c();\n"
                                     "  initial #1 $display(\"%b %b %b\", "
                                     "a.w, b.w, c.w);\n"
                                     "endmodule\n",
                                 f),
            "0 1 z\n");
}
