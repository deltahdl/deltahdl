#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

// §23.3.3: an inout port connection is a non-strength-reducing (bidirectional)
// transistor connection between the internal and external nets, rather than a
// one-directional continuous assignment. A value driven inside the instance
// therefore passes out to the connected parent net undiminished.
TEST(PortConnectionRulesSimulation,
     InoutPortConductsValueToParentUndiminished) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire [7:0] pad);\n"
      "  assign pad = 8'h3C;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.pad(bus));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

// §23.3.3: the item on the source side of a port connection may be an
// expression, not just a bare identifier, and the connection acts as a
// continuous assignment of that source to the port's sink. A widening (rather
// than truncating) case keeps this observation tied to the head rule and
// distinct from the width-limited forms owned by other subclauses.
TEST(PortConnectionRulesSimulation, ExpressionSourceOnInputPortDrivesSink) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  logic [7:0] p;\n"
                "  logic [7:0] q;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(p | q), .b(result));\n"
                "  initial begin p = 8'hF0; q = 8'h0F; end\n"
                "endmodule\n",
                "result"),
      0xFFu);
}

// §23.3.3: compatible port types follow the same rules as assignment
// compatibility (§6.22.3). A narrower assignment-compatible source is
// width-converted (zero-extended for an unsigned source) into a wider input
// port exactly as a variable assignment would convert it, observed at runtime.
TEST(PortConnectionRulesSimulation,
     AssignmentCompatibleWidthConversionPropagates) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  logic [3:0] narrow;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(narrow), .b(result));\n"
                "  initial narrow = 4'hA;\n"
                "endmodule\n",
                "result"),
      0x0Au);
}

// §23.3.3: an output port connection is a continuous assignment whose source is
// internal to the instance and whose sink is the connected item in the parent.
// The child drives its output and the parent variable observes it — the source
// side of the connection being inside the instance is a distinct form from the
// input-port case, where the source is external.
TEST(PortConnectionRulesSimulation, OutputPortConnectionDrivesParentSink) {
  EXPECT_EQ(RunAndGet("module child(output logic [7:0] y);\n"
                      "  assign y = 8'h5A;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  logic [7:0] result;\n"
                      "  child u(.y(result));\n"
                      "endmodule\n",
                      "result"),
            0x5Au);
}

// §23.3.3 consuming §10.3: the value supplied to an input port may itself be
// produced by a continuous assignment in the instantiating module. Built from
// real continuous-assignment syntax, the port connection carries that
// continuously-driven source through to the sink inside the instance.
TEST(PortConnectionRulesSimulation,
     ContinuousAssignSourceFlowsThroughInputPort) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  logic [7:0] base;\n"
                "  logic [7:0] feed;\n"
                "  logic [7:0] result;\n"
                "  assign feed = base ^ 8'hFF;\n"
                "  child u(.a(feed), .b(result));\n"
                "  initial base = 8'h0F;\n"
                "endmodule\n",
                "result"),
      0xF0u);
}

// §23.3.3 consuming §6.22.3: a 2-state source is assignment-compatible with a
// 4-state port, so a `bit` vector connected to a `logic` input port propagates
// its value through the connection unchanged. This exercises the 2-state
// operand path, distinct from the width-conversion form above.
TEST(PortConnectionRulesSimulation, TwoStateSourcePropagatesThroughInputPort) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  bit [7:0] two_state;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(two_state), .b(result));\n"
                "  initial two_state = 8'hC3;\n"
                "endmodule\n",
                "result"),
      0xC3u);
}

// §23.3.3: the source item of a port connection may be a parameter (constant)
// reference rather than a variable, which resolves through a different path
// than a signal reference. The elaborated constant is carried to the sink.
TEST(PortConnectionRulesSimulation, ParameterValueSourceDrivesInputPort) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  parameter logic [7:0] P = 8'h77;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(P), .b(result));\n"
                "endmodule\n",
                "result"),
      0x77u);
}

}  // namespace
