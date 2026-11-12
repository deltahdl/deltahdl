#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SyncDriveSignalsElab, ContinuousAssignToOutputSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  assign data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    7, "14.16.2"));
}

TEST(SyncDriveSignalsElab, ContinuousAssignToInoutSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  assign data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    7, "14.16.2"));
}

TEST(SyncDriveSignalsElab, ContinuousAssignToOutputSignalBitSelectErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  assign data[2] = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to clocking output variable 'data'",
                    8, "14.16.2"));
}

TEST(SyncDriveSignalsElab, ProceduralAssignToOutputSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial assign data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to variable 'data', which is associated with a "
                            "clocking output, is not allowed",
                            7, "14.16.2"));
}

TEST(SyncDriveSignalsElab, ForceToOutputSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force data = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to variable 'data', which is associated with a "
                            "clocking output, is not allowed",
                            7, "14.16.2"));
}

TEST(SyncDriveSignalsElab, ForceToOutputSignalBitSelectErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data;\n"
             "  logic r;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial force data[2] = r;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural continuous assignment (assign/force) "
                            "to variable 'data', which is associated with a "
                            "clocking output, is not allowed",
                            8, "14.16.2"));
}

TEST(SyncDriveSignalsElab, PrimitiveDriveToOutputSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  and g1(data, a, b);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive output drives variable 'data', which is "
                            "associated with a clocking output",
                            7, "14.16.2"));
}

TEST(SyncDriveSignalsElab, PrimitiveDriveToInoutSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic data, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  and g1(data, a, b);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive output drives variable 'data', which is "
                            "associated with a clocking output",
                            7, "14.16.2"));
}

TEST(SyncDriveSignalsElab, MultiOutputBufDriveToOutputSignalErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic o1, data, in;\n"
             "  clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  buf g(o1, data, in);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive output drives variable 'data', which is "
                            "associated with a clocking output",
                            7, "14.16.2"));
}

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

TEST(SyncDriveSignalsElab, AssociatedVariableIsTheExpressionsSignal) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk, v, o, a, b;\n"
             "  clocking cb @(posedge clk);\n"
             "    output o = v;\n"
             "    output w = {a, b};\n"
             "  endclocking\n"
             "  assign v = 1'b1;\n"
             "  assign o = 1'b0;\n"
             "  assign b = 1'b1;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment to clocking output "
                            "variable 'v'",
                            7, "14.16.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "continuous assignment to clocking output "
                             "variable 'o'",
                             8, "14.16.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "continuous assignment to clocking output "
                            "variable 'b'",
                            9, "14.16.2"));
}

const char* const kAcceptedClockingOutputNetDrivers[] = {
    "  wire w = d;\n",
    "  wire w;\n  sub u(w);\n",
    "  wire w;\n  inv g(w, d);\n",
};

TEST(SyncDriveSignalsElab, ANetDeclarationPortOrUdpDriverOfAClockingOutputNet) {
  for (const char* drivers : kAcceptedClockingOutputNetDrivers) {
    SCOPED_TRACE(drivers);
    EXPECT_TRUE(ElabOk(std::string("primitive inv(output o, input i);\n"
                                   "  table 0 : 1; 1 : 0; endtable\n"
                                   "endprimitive\n"
                                   "module sub(output wire o);\n"
                                   "  assign o = 1'b0;\n"
                                   "endmodule\n"
                                   "module m;\n"
                                   "  logic clk = 0;\n"
                                   "  logic d = 0;\n") +
                       drivers +
                       "  clocking cb @(posedge clk); output w; endclocking\n"
                       "endmodule\n"));
  }
}

const char* const kRefusedClockingOutputNetDrivers[] = {
    "  wire w;\n  assign w = d;\n",
    "  wire [3:0] w;\n  assign w[1] = d;\n",
    "  wire w;\n  buf (w, d);\n",
    "  wire w;\n  initial begin force w = d; #1 release w; end\n",
    "  wand w;\n  assign w = d;\n",
    "  wor w;\n  assign w = d;\n",
    "  tri w;\n  assign w = d;\n",
    "  typedef logic T;\n  nettype T nt;\n  nt w;\n  assign w = d;\n",
};

TEST(SyncDriveSignalsElab,
     DISABLED_AContinuousGateOrForceDriverOfAClockingOutputNet) {
  for (const char* drivers : kRefusedClockingOutputNetDrivers) {
    SCOPED_TRACE(drivers);
    EXPECT_TRUE(ElabOk(std::string("module m;\n"
                                   "  logic clk = 0;\n"
                                   "  logic d = 0;\n") +
                       drivers +
                       "  clocking cb @(posedge clk); output w; endclocking\n"
                       "endmodule\n"));
  }
}

}  // namespace
