#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §23.3.3: "Each port connection shall be a continuous assignment of source
// to sink, where one connected item shall be a signal source and the other
// shall be a signal sink. The assignment shall be a continuous assignment
// from source to sink for input or output ports." The value on the external
// source signal shall propagate through the port to the internal sink at
// simulation time.
TEST(PortConnectionRulesSimulation, InputPortPropagatesSourceValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  initial src = 8'hA5;\n"
      "  child u(.a(src), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// §23.3.3: "If the internal and external connections to a port are of
// user-defined nettypes, they shall be of matching nettypes and shall be
// merged into a single simulated net." A signal of the matching nettype on
// the external side shall drive the internal port at runtime.
TEST(PortConnectionRulesSimulation, MatchingNettypePropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  nettype logic [7:0] mytype;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  initial src = 8'h5A;\n"
      "  child u(.a(src), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

}  // namespace
