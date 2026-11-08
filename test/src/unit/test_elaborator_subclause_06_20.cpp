#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstAssignElaboration, ABitSelectWriteToAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[3] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, APartSelectWriteToAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  initial P[7:4] = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AConcatenationWriteToAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial {i, P} = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromATaskBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  task t;\n"
      "    P = 7;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterFromAFunctionBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  function int fn;\n"
      "    P = 7;\n"
      "    return P;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInsideForkIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial fork\n"
      "    P = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (P = 0; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; P = P + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, ABitSelectWriteToALocalparamIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam logic [7:0] L = 8'hFF;\n"
      "  initial L[0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'L'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AnElementWriteToAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S[0] = \"X\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAVariableThroughABitSelectIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic [7:0] v;\n"
             "  initial v[3] = 1'b0;\n"
             "endmodule\n"));
}

TEST(ConstAssignElaboration, APutcOnAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S.putc(0, \"X\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, AnItoaOnAStringParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter string S = \"abc\";\n"
      "  initial S.itoa(7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, ARealtoaOnAStringLocalparamIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam string S = \"abc\";\n"
      "  initial S.realtoa(1.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'S'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration, APutcOnAStringVariableIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s = \"abc\";\n"
             "  initial s.putc(0, \"X\");\n"
             "endmodule\n"));
}

TEST(ConstAssignElaboration, AGetcOnAStringParameterIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  parameter string S = \"abc\";\n"
             "  byte b;\n"
             "  initial b = S.getc(0);\n"
             "endmodule\n"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInABeginEndBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial begin\n"
      "    P = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAnIfBranchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial if (i == 0) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAnElseBranchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial if (i == 0) i = 1; else P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAWhileBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial while (i < 2) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInAForBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; i = i + 1) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInACaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial\n"
      "    case (i)\n"
      "      0: P = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            6, "6.20"));
}

TEST(ConstAssignElaboration, AWriteToAParameterInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial randcase 1: P = 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            3, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic ok;\n"
      "  initial assert (ok) P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic ok;\n"
      "  initial assert (ok) else P = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            4, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { P = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            5, "6.20"));
}

TEST(ConstAssignElaboration,
     AWriteToAParameterInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int P = 4;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { P = 1; };\n"
      "      a : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'P'",
                            6, "6.20"));
}

}  // namespace
