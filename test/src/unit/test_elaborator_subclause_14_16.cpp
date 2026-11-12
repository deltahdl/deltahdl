#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SyncDriveElab, ContinuousAssignToClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic [7:0] data;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  assign data = 8'h00;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    6, "14.16.2"));
}

TEST(SyncDriveElab, WriteToInputClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial cb.data <= 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.data'", 5, "14.3"));
}

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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    7, "14.16.2"));
}

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

TEST(SyncDriveElab, ContinuousOrBlockingWriteToAClockvarErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] q = 1;\n"
      "  clocking cb @(posedge clk);\n"
      "    output q;\n"
      "  endclocking\n"
      "  assign cb.q = 3;\n"
      "  initial begin\n"
      "    cb.q = 3;\n"
      "    cb.q <= 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment to a clockvar", 7, "14.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "not by a blocking assignment", 9, "14.16"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "not by a blocking assignment", 10, "14.16"));
}

TEST(SyncDriveElab, DriveFormInSubroutineAndGenerateErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] q;\n"
             "  clocking cb @(posedge clk);\n"
             "    output q;\n"
             "  endclocking\n"
             "  task t;\n"
             "    cb.q = 1;\n"
             "    cb.q <= #4 2;\n"
             "    force cb.q = 3;\n"
             "  endtask\n"
             "  if (1) begin : g\n"
             "    initial cb.q = 4;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "not by a blocking assignment", 8, "14.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "intra-assignment delay (#) is not a legal "
                            "synchronous drive",
                            9, "14.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to a clocking output variable",
                            10, "14.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "not by a blocking assignment", 13, "14.16"));
}

struct HierarchicalClockvarWrite {
  const char* item;
  const char* message;
  const char* subclause;
};

const HierarchicalClockvarWrite kHierarchicalClockvarWrites[] = {
    {"initial u.cb.a <= #4 8'd1;",
     "intra-assignment delay (#) is not a legal synchronous drive", "14.16"},
    {"initial u.cb.i <= 8'd1;", "write to input clockvar", "14.3"},
    {"initial force u.cb.a = 8'd1;",
     "procedural continuous assignment (assign/force)", "14.16"},
    {"initial assign u.cb.a = 8'd1;",
     "procedural continuous assignment (assign/force)", "14.16"},
    {"assign u.cb.a = 8'd1;", "continuous assignment to a clockvar", "14.16"},
};

TEST(SyncDriveElab, DISABLED_AForbiddenWriteToAHierarchicalClockvarIsReported) {
  for (const auto& w : kHierarchicalClockvarWrites) {
    SCOPED_TRACE(w.item);
    ElabFixture f;
    ElaborateSrc(std::string("module unit(input logic clk);\n"
                             "  logic [7:0] a = 0, i = 0;\n"
                             "  clocking cb @(posedge clk);\n"
                             "    output a;\n"
                             "    input i;\n"
                             "  endclocking\n"
                             "endmodule\n"
                             "module top;\n"
                             "  logic clk = 0;\n"
                             "  unit u(clk);\n"
                             "  ") +
                     w.item + "\nendmodule\n",
                 f, "top");
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), w.message, 11, w.subclause));
  }
}

TEST(SyncDriveElab, ASynchronousDriveToAHierarchicalOutputClockvarIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module unit(input logic clk);\n"
             "  logic [7:0] a = 0;\n"
             "  clocking cb @(posedge clk);\n"
             "    output a;\n"
             "  endclocking\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  unit u(clk);\n"
             "  initial u.cb.a <= 8'd1;\n"
             "endmodule\n"));
}

}  // namespace
