#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SyncDriveElab, ContinuousAssignToClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  assign data = 8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(SyncDriveElab, WriteToInputClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial cb.data <= 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.16: a leading cycle delay (## ...) is the only timing control allowed on
// a synchronous drive; the whole-clockvar drive elaborates cleanly.
TEST(SyncDriveElab, CycleDelayDriveOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= ##2 r;\n"
             "endmodule\n"));
}

// §14.16: a regular intra-assignment delay (# ...) is not a legal synchronous
// drive form, even though the same statement with a cycle delay is legal.
TEST(SyncDriveElab, IntraAssignDelayDriveErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= #4 r;\n"
             "endmodule\n"));
}

// §14.16: it is illegal to write to a clockvar with a procedural continuous
// assignment; forcing an ordinary (non-clockvar) variable is legal.
TEST(SyncDriveElab, ForceOrdinaryVariableOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, q, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force q = r;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, ForceToOutputClockvarErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force cb.data = r;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, ProceduralAssignToOutputClockvarErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial assign cb.data = r;\n"
             "endmodule\n"));
}

// §14.16: the clockvar_expression of a synchronous drive may be a bit-select,
// slice, or the whole clockvar, but never a concatenation.
TEST(SyncDriveElab, WholeClockvarDriveOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [3:0] a, b, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output a, b;\n"
             "  endclocking\n"
             "  initial cb.a <= r;\n"
             "endmodule\n"));
}

TEST(SyncDriveElab, ConcatenationDriveTargetErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [3:0] a, b;\n"
             "  logic [7:0] r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output a, b;\n"
             "  endclocking\n"
             "  initial {cb.a, cb.b} <= r;\n"
             "endmodule\n"));
}

// §14.16: a bit-select of a clockvar is one of the permitted drive targets.
TEST(SyncDriveElab, BitSelectDriveOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data[2] <= r;\n"
             "endmodule\n"));
}

// §14.16: a slice (part-select) of a clockvar is also a permitted drive target.
TEST(SyncDriveElab, SliceDriveOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic [3:0] r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data[3:0] <= r;\n"
             "endmodule\n"));
}

// §14.16: the prohibition on a regular intra-assignment delay (# ...) also
// applies when the drive target is a bit-select of a clockvar.
TEST(SyncDriveElab, IntraAssignDelayOnBitSelectDriveErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data[2] <= #1 r;\n"
             "endmodule\n"));
}

// §14.16 intro: the drivable clocking block outputs are those declared `output`
// *or* `inout`. A synchronous drive to an inout clockvar is the legal way to
// write it, so it must elaborate cleanly -- the direction check rejects only a
// write to an `input` clockvar, never a drive to an inout one.
TEST(SyncDriveElab, SyncDriveToInoutClockvarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial cb.data <= r;\n"
             "endmodule\n"));
}

// §14.16: the write-to-a-clockvar prohibition applies to inout clockvars as
// well as output ones. A continuous assignment to the signal tied to an inout
// clockvar is illegal exactly as it is for an output clockvar.
TEST(SyncDriveElab, ContinuousAssignToInoutClockvarErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  assign data = 8'h00;\n"
             "endmodule\n"));
}

// §14.16: likewise, a procedural continuous assignment (force) to an inout
// clockvar is illegal -- only the synchronous drive syntax may write it.
TEST(SyncDriveElab, ForceToInoutClockvarErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial force cb.data = r;\n"
             "endmodule\n"));
}

// §14.16: the write-to-a-clockvar prohibition covers the `assign` form of a
// procedural continuous assignment for an inout clockvar as well, completing
// the {assign, force} x {output, inout} matrix of illegal write forms.
TEST(SyncDriveElab, ProceduralAssignToInoutClockvarErrors) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial assign cb.data = r;\n"
             "endmodule\n"));
}

// §14.16: the right-hand side of a synchronous drive may be any valid
// expression that is assignment compatible with the driven signal -- not just
// a bare identifier or literal. An operator expression as the drive value
// elaborates cleanly.
TEST(SyncDriveElab, DriveExpressionMayBeArbitraryExpression) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= (a & b) | 8'h0F;\n"
             "endmodule\n"));
}

}  // namespace
