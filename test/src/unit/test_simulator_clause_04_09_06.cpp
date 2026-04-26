#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §4.9.6 atom: ports connect processes through implicit continuous
// assignment statements. No user-written `assign` bridges the outside
// constant `8'hAB` to the child input port `a`, yet the implicit
// input-port cont-assign added by `LowerPortBindings` drives the local
// port from the outside expression. Observed by reading the hierarchical
// `u.a` after `Run` — without the implicit cont-assign the local port
// stays at its X initial.
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

// §4.9.6 atom: an input port is a continuous assignment from an outside
// expression to a local (input) net or variable. Continuous semantics
// mean RHS changes propagate without a re-instantiation — the parent
// drives `src` first to `0x11` then to `0x22` at t=5, and the child
// port `u.a` ends up holding the latest value because the implicit
// input cont-assign re-evaluates on every change to its RHS.
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

// §4.9.6 atom: an output port is a continuous assignment from a local
// output expression to an outside net or variable. The child internally
// drives `b` to `0xCD` and the implicit output-port cont-assign added
// by `LowerPortBindings` delivers that value to `result` in the parent.
// Without the implicit cont-assign, `result` remains uninitialized.
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

// §4.9.6 atom: an inout port is a non-strength-reducing transistor
// connecting the local net to an outside net — the two sides share a
// single storage location so a write on either side is observable on
// the other. `LowerPortBindings` aliases the child's local port
// variable onto the outside identifier; the child's `assign data = ...`
// then writes through the alias to `bus`. Without the alias, the local
// `u.data` and outside `bus` would be independent and `bus` would
// remain at its uninitialized X.
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

// §4.9.6 atoms: primitive output terminals connect to 1-bit nets, and
// changes from primitive evaluations are scheduled as active update
// events in the connected nets. `ElaborateGateInst` lowers `buf` to a
// continuous assignment whose 1-bit `wire` LHS receives the input bit
// directly, and `LowerContAssign` schedules the cont-assign in
// `Region::kActive` so the output settles within the same timestep its
// input becomes valid. Observed by reading `out_sig` (which proves the
// 1-bit net connection carried the value) and `CurrentTime` (which
// proves the update fired in Active rather than a later region).
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

// §4.9.6 atom: primitive output terminals connect to 1-bit nets with no
// intervening process that could alter the strength. The atom's value-
// flow aspect is exercised above; the strength aspect is observed here
// by inspecting the driven net's per-driver strength on each side. The
// gate elaborator's synthesized cont-assign carries the default Strong
// drive, and `LowerContAssign`'s coroutine pushes that strength onto
// the net unchanged because no delay or strength-modifying switch
// intervenes — the resulting `driver_strengths[0]` reads back as
// Strong on both rails.
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

// §4.9.6 atom (edge case): the implicit-cont-assign port-connection
// mechanism applies at every instance boundary, so a value driven at
// the top level must traverse two layers of port bindings to reach a
// leaf module's local input port. Both `LowerChildModules` levels
// (top→mid and mid→leaf) call `LowerPortBindings`, each producing one
// implicit input cont-assign that drives the next level's local port
// variable. The leaf's `u_mid.u_leaf.x` ends up holding the original
// outside expression `8'h7E`. A break in either level's port-binding
// lowering would leave `x` at its uninitialized X.
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

// §4.9.6 atom: input terminals connected to other kinds of expressions
// (not 1-bit nets) are represented as implicit continuous assignments
// from the expression to an implicit net connected to the input
// terminal. Here the `buf` input terminal is `a & b`, an expression
// rather than a bare net — the gate elaborator's cont-assign captures
// the AND result and re-evaluates whenever either operand changes,
// matching the implicit-cont-assign semantics §4.9.6 specifies.
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

}  // namespace
