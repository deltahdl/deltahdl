
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

// §23.3.3.7.1 consuming §23.3.3.7 (Table 23-1) end-to-end through simulation:
// the interconnect net iwire, built from real module/instance source and driven
// through the full pipeline, merges a wire net driving 1 and a wand net driving
// 0 into a single simulated net. Because the merged net takes the dominating
// wand type, the two drivers combine to a defined value rather than
// conflicting. Had the merge left the net as interconnect (resolved as a plain
// wire), the 1/0 conflict would produce x, so observing a known resolved value
// confirms the merged net type was applied at run time.
TEST(InterconnectPortConnectionSimulation,
     InterconnectMergedAcrossDissimilarPortsResolvesToDefinedValue) {
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
  EXPECT_TRUE(var->value.IsKnown());
}

}  // namespace
