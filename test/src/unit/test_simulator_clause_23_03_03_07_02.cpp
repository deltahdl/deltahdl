
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §23.3.3.7.2 at runtime: an interconnect net on a primitive terminal behaves
// as a plain wire. The rule is blind to the gate kind, so one representative
// per rule-relevant runtime form is kept: interconnect on a gate input carries
// a driven value into the primitive, interconnect on a gate output receives the
// primitive's value, and interconnect as the sole terminal of a source
// primitive receives that primitive's value. The input case is fed through a
// module port (§23.3.3.7.1) so the value reaching the gate is produced by real
// source syntax.

namespace {

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnAndGateInputPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module driver(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  interconnect ic;\n"
      "  wire y;\n"
      "  driver d(.a(ic));\n"
      "  and (y, ic, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation,
     InterconnectOnAndGateOutputReceivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire a, b;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b1;\n"
      "  interconnect ic;\n"
      "  and (ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InterconnectPrimitiveTerminalSimulation, InterconnectOnPullupReceivesOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect ic;\n"
      "  pullup (ic);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
