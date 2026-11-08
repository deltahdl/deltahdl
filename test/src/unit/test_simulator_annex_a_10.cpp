#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortInitializerSimulation, TopOutputPortHoldsItsInitializer) {
  SimFixture f;
  auto out = RunCapture(
      "module m(output logic [3:0] q = 4'd9);\n"
      "  initial $display(\"q=%0d\", q);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "q=9\n");
}

TEST(PortInitializerSimulation, InitializerReadsTheModulesOwnParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m #(parameter int START = 6) (output int q = START + 1);\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(PortInitializerSimulation, ChildOutputPortInitializerReachesTheParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output logic [7:0] q = 8'h5A, output logic [7:0] r = "
      "8'h3);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] seen;\n"
      "  child u(.q(seen), .r());\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
  auto* r = f.ctx.FindVariable("u.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 3u);
}

}  // namespace
