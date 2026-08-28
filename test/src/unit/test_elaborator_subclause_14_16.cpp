#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  // The rule a continuous assignment to the variable tied to an output clockvar
  // breaks is §14.16.2's, not §14.16's; the report names the subclause it
  // enforces.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    6, "14.16.2"));
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
  // The direction an input clockvar may be accessed in is §14.3's rule, and
  // that is the subclause the report enforcing it names.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 5, "14.3"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data <= #4 r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "intra-assignment delay (#) is not a legal "
                            "synchronous drive to a clocking output variable",
                            7, "14.16"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force cb.data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to a clocking output variable is not allowed",
                            7, "14.16"));
}

TEST(SyncDriveElab, ProceduralAssignToOutputClockvarErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial assign cb.data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to a clocking output variable is not allowed",
                            7, "14.16"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [3:0] a, b;\n"
             "  logic [7:0] r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output a, b;\n"
             "  endclocking\n"
             "  initial {cb.a, cb.b} <= r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a concatenation is not a legal synchronous drive "
                            "target for a clocking output variable",
                            8, "14.16"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial cb.data[2] <= #1 r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "intra-assignment delay (#) is not a legal "
                            "synchronous drive to a clocking output variable",
                            8, "14.16"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  assign data = 8'h00;\n"
             "endmodule\n",
             f));
  // The target is the bare variable the inout clockvar is tied to, not the
  // clockvar, so the rule broken is §14.16.2's and that is what the report
  // names.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    7, "14.16.2"));
}

// §14.16: likewise, a procedural continuous assignment (force) to an inout
// clockvar is illegal -- only the synchronous drive syntax may write it.
TEST(SyncDriveElab, ForceToInoutClockvarErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial force cb.data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to a clocking output variable is not allowed",
                            7, "14.16"));
}

// §14.16: the write-to-a-clockvar prohibition covers the `assign` form of a
// procedural continuous assignment for an inout clockvar as well, completing
// the {assign, force} x {output, inout} matrix of illegal write forms.
TEST(SyncDriveElab, ProceduralAssignToInoutClockvarErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial assign cb.data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to a clocking output variable is not allowed",
                            7, "14.16"));
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

// §14.16 states the form a synchronous drive takes and names no statement the
// form is not required in, but Elaborator::WalkStmtsForSyncDriveForm wrote out
// six of the thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. This is the file's own
// IntraAssignDelayDriveErrors written in a randsequence production code block,
// which A.6.12 gives `{ { data_declaration } { statement_or_null } }`, so the
// drive reached neither CheckSyncDriveAssign nor CheckSyncDriveProcContAssign.
TEST(SyncDriveElab, IntraAssignDelayDriveInRandsequenceCodeBlockErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { cb.data <= #4 r; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "intra-assignment delay (#) is not a legal "
                            "synchronous drive to a clocking output variable",
                            9, "14.16"));
}

}  // namespace
