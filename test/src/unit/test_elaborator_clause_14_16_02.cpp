#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §14.16.2: it shall be illegal to write the variable underlying an output
// clockvar with a continuous assignment. This targets the bare signal (data),
// not the clockvar member (cb.data).
TEST(SyncDriveSignalsElab, ContinuousAssignToOutputSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  assign data = r;\n"
             "endmodule\n"));
}

// §14.16.2: the same prohibition covers an inout clockvar's underlying signal.
TEST(SyncDriveSignalsElab, ContinuousAssignToInoutSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  assign data = r;\n"
             "endmodule\n"));
}

// §14.16.2: a procedural continuous assignment (assign) to the underlying
// signal of an output clockvar is illegal.
TEST(SyncDriveSignalsElab, ProceduralAssignToOutputSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial assign data = r;\n"
             "endmodule\n"));
}

// §14.16.2: a procedural continuous assignment via force to the underlying
// signal of an output clockvar is illegal.
TEST(SyncDriveSignalsElab, ForceToOutputSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force data = r;\n"
             "endmodule\n"));
}

// §14.16.2: the force prohibition extends to a bit-select of the underlying
// signal -- the root variable is still associated with an output clockvar.
TEST(SyncDriveSignalsElab, ForceToOutputSignalBitSelectErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force data[2] = r;\n"
             "endmodule\n"));
}

// §14.16.2: it shall be illegal to drive the underlying signal of an output
// clockvar from a primitive (here, an and-gate output terminal).
TEST(SyncDriveSignalsElab, PrimitiveDriveToOutputSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  and g1(data, a, b);\n"
             "endmodule\n"));
}

// §14.16.2: the primitive prohibition applies equally to the signal underlying
// an inout clockvar, which carries an output side.
TEST(SyncDriveSignalsElab, PrimitiveDriveToInoutSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  and g1(data, a, b);\n"
             "endmodule\n"));
}

// §14.16.2: a buf/not primitive may have several output terminals (every
// terminal but the last). Driving an output clockvar's underlying signal from a
// non-first buf output terminal is still illegal.
TEST(SyncDriveSignalsElab, MultiOutputBufDriveToOutputSignalErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic o1, data, in;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  buf g(o1, data, in);\n"
             "endmodule\n"));
}

// §14.16.2: conversely, the last terminal of a buf is its input, so a buf whose
// input happens to be an output clockvar's signal is not a driver of it and is
// legal. This pins down that only output terminals are checked.
TEST(SyncDriveSignalsElab, BufInputTerminalIsOutputSignalOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic o1, o2, data;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  buf g(o1, o2, data);\n"
             "endmodule\n"));
}

// §14.16.2: the restriction is specific to output/inout clockvars. The signal
// underlying an input clockvar is fed by external drivers, so driving it from a
// primitive is legal.
TEST(SyncDriveSignalsElab, PrimitiveDriveToInputSignalOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  and g1(data, a, b);\n"
             "endmodule\n"));
}

// §14.16.2: a continuous assignment to an ordinary variable that is not bound
// to any clocking output remains legal.
TEST(SyncDriveSignalsElab, ContinuousAssignToUnrelatedVariableOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, other, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  assign other = r;\n"
             "endmodule\n"));
}

// §14.16.2: a procedural assignment (not a continuous one) to the underlying
// signal is permitted -- the variable simply holds the assigned value until the
// next assignment. Only continuous/procedural-continuous/primitive drivers are
// forbidden.
TEST(SyncDriveSignalsElab, ProceduralBlockingAssignToOutputSignalOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial data = r;\n"
             "endmodule\n"));
}

}  // namespace
