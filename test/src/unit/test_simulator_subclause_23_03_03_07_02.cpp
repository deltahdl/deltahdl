#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnAndGateInputPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module driver(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  driver d(.a(ic));\n"
      "  and (y, ic, 1'b1);\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnAndGateOutputReceivesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b1;\n"
      "  interconnect ic;\n"
      "  and (ic, a, b);\n"
      "endmodule\n",
      f, "ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation, InterconnectOnPullupReceivesOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  interconnect ic;\n"
      "  pullup (ic);\n"
      "endmodule\n",
      f, "ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
