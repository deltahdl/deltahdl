#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionSchedulingSim, InputPortDrivesLocalFromOutsideExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("u.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xABu);
}

TEST(PortConnectionSchedulingSim, InputPortFollowsOutsideChangesContinuously) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  initial begin\n"
      "    src = 8'h11;\n"
      "    #5 src = 8'h22;\n"
      "  end\n"
      "  child u(src);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("u.a")->value.ToUint64(), 0x22u);
}

TEST(PortConnectionSchedulingSim, OutputPortDrivesOutsideFromLocalExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] b);\n"
      "  assign b = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 0xCDu);
}

TEST(PortConnectionSchedulingSim, InoutPortSharesStorageWithOutsideNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(bus);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(PortConnectionSchedulingSim, PrimitiveEvaluationProducesActiveUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic in_sig;\n"
      "  wire out_sig;\n"
      "  initial in_sig = 1'b1;\n"
      "  buf b(out_sig, in_sig);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* out = f.ctx.FindVariable("out_sig");
  ASSERT_NE(out, nullptr);
  EXPECT_EQ(out->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(PortConnectionSchedulingSim, PrimitiveOutputPreservesDriverStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic in_sig;\n"
      "  wire out_sig;\n"
      "  initial in_sig = 1'b1;\n"
      "  buf b(out_sig, in_sig);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* net = f.ctx.FindNet("out_sig");
  ASSERT_NE(net, nullptr);
  ASSERT_FALSE(net->driver_strengths.empty());
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kStrong);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kStrong);
}

TEST(PortConnectionSchedulingSim, NestedHierarchyPropagatesPortConnections) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module leaf(input logic [7:0] x);\n"
      "endmodule\n"
      "module mid(input logic [7:0] y);\n"
      "  leaf u_leaf(y);\n"
      "endmodule\n"
      "module top;\n"
      "  mid u_mid(8'h7E);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("u_mid.u_leaf.x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x7Eu);
}

TEST(PortConnectionSchedulingSim, PrimitiveInputAcceptsExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire out_sig;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "  end\n"
      "  buf bg(out_sig, a & b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("out_sig")->value.ToUint64() & 1u, 1u);
}

// A primitive evaluation triggered by an input change after time zero schedules
// an active update event in the connected output net, so the output tracks the
// later input value rather than only the time-zero one.
TEST(PortConnectionSchedulingSim,
     PrimitiveEvaluationSchedulesActiveUpdateOnInputChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic in_sig;\n"
      "  wire out_sig;\n"
      "  initial begin\n"
      "    in_sig = 1'b0;\n"
      "    #5 in_sig = 1'b1;\n"
      "  end\n"
      "  buf b(out_sig, in_sig);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("out_sig")->value.ToUint64() & 1u, 1u);
}

// §4.9.6 represents the local side of an input port as a net OR a variable. The
// tests above drive a variable local; this covers the net alternative: an input
// port declared as a net still receives the implicit continuous assignment from
// the outside expression and takes its value.
TEST(PortConnectionSchedulingSim, InputPortNetDrivenFromOutsideExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u(8'h5C);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("u.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x5Cu);
}

// §4.9.6 represents the outside side of an output port as a net OR a variable.
// The test above connects an output port to an outside variable; this covers
// the net alternative: the implicit continuous assignment drives an outside
// net.
TEST(PortConnectionSchedulingSim, OutputPortDrivesOutsideNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] b);\n"
      "  assign b = 8'h3D;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0x3Du);
}

// §4.9.6 distinguishes a primitive input terminal fed by a 1-bit structural net
// expression (connected directly) from one fed by some other expression
// (represented through an implicit net). This drives a bit-select of a net --
// a structural net expression -- into the input terminal and observes the
// output track it.
TEST(PortConnectionSchedulingSim,
     PrimitiveInputAcceptsStructuralNetExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] src;\n"
      "  wire [3:0] bus;\n"
      "  wire out_sig;\n"
      "  assign bus = src;\n"
      "  initial src = 4'b1000;\n"
      "  buf b(out_sig, bus[3]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("out_sig")->value.ToUint64() & 1u, 1u);
}

}  // namespace
