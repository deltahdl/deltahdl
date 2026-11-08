#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InterconnectPortConnectionSimulation,
     ExternalInterconnectInternalWirePropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f, "ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPortConnectionSimulation,
     ExternalInterconnectInternalWandPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f, "ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPortConnectionSimulation,
     InternalInterconnectExternalWirePropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module drv(output wire o);\n"
      "  assign o = 1'b1;\n"
      "endmodule\n"
      "module child(output interconnect a);\n"
      "  drv d(.o(a));\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPortConnectionSimulation,
     InterconnectMergedAcrossDissimilarPortsResolvesToDefinedValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module dut1(inout wire w);\n"
      "  assign w = 1;\n"
      "endmodule\n"
      "module dut2(inout wand w);\n"
      "  assign w = 0;\n"
      "endmodule\n"
      "module netlist;\n"
      "  interconnect iwire;\n"
      "  dut1 child1(iwire);\n"
      "  dut2 child2(iwire);\n"
      "endmodule\n",
      f, "iwire");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
}

}  // namespace
