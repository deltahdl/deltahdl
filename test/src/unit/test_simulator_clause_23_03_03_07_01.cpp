
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- R1+R3: If only one net is an interconnect net, the merged net shall be
//     the type of the other net; values propagate through the merged net. ---

TEST(InterconnectPortConnectionSimulation,
     ExternalInterconnectInternalWirePropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPortConnectionSimulation,
     ExternalInterconnectInternalWandPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  child u(.a(ic));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPortConnectionSimulation,
     InternalInterconnectExternalWirePropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output interconnect a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// R1+R3: Interconnect merged with multiple child ports of different types

TEST(InterconnectPortConnectionSimulation,
     InterconnectMergedWithMultipleChildPortsPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("iwire");
  ASSERT_NE(var, nullptr);
}

}  // namespace
