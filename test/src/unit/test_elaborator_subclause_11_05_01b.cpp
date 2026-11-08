#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

TEST(RealSelect, BitSelectOfARealArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, PartSelectOfARealArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealArrayElementAsATargetIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial arr[i][0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(SelectElaboration, BitSelectOfAScalarArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s[4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = s[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
}

TEST(SelectElaboration, BitSelectOfAPackedArrayElementIsStillLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem[4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = mem[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SelectElaboration, BitSelectOfATwoDimensionalArrayElementIsStillLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem[4][4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = mem[i][i][0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealSelect, BitSelectOfARealParameterPortNamesTheRealRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter real P = 1.5);\n"
      "  wire y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 3,
                            "11.5.1"));
}

TEST(RealSelect, PartSelectOfARealParameterPortNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter real P = 1.5);\n"
      "  wire [3:0] y;\n"
      "  assign y = P[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real parameter is illegal", 3,
                            "11.5.1"));
}

TEST(RealSelect, BitSelectOfARealLocalparamPortNamesTheRealRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(localparam real P = 1.5);\n"
      "  wire y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 3,
                            "11.5.1"));
}

TEST(RealSelect, RealParameterPortWithNoSelectIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter real P = 1.5);\n"
      "  real v;\n"
      "  assign v = P;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealSelect, BitSelectOfARealArrayElementInAlwaysCombIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  always_comb v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealArrayElementInAlwaysFfIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  logic clk;\n"
      "  always_ff @(posedge clk) v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 6,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealArrayElementInAlwaysLatchIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  always_latch v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealArrayElementInFinalIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  final v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(SelectElaboration, ScalarSelectInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = x[0]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            6, "11.5.1"));
}

TEST(SelectElaboration, RealSelectInAnAssertPassArmIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial assert (1) y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(SelectElaboration, IndexedPartSelectWidthInAForInitIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [7:0] y;\n"
      "  initial for (y = data[0+:w]; w < 2; w = w + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 5, "11.5.1"));
}

TEST(SelectElaboration, PartSelectInARandsequenceCodeBlockIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = data[7:4]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealSelect, BitSelectOfARealInAConditionalConditionIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  assign v = r[0] ? 1.0 : 2.0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealInAConditionalTrueArmIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  logic c;\n"
      "  assign v = c ? r[0] : 1.0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealInAConditionalFalseArmIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  logic c;\n"
      "  assign v = c ? 1.0 : r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealInACallArgumentIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  real v;\n"
      "  function automatic real ident(input real a);\n"
      "    ident = a;\n"
      "  endfunction\n"
      "  assign v = ident(r[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 7,
                            "6.12"));
}

TEST(RealSelect, PartSelectOfARealInAConcatenationNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic [4:0] y;\n"
      "  assign y = {r[3:0], 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealInAPartSelectBoundIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] y;\n"
      "  assign y = d[3:r[0]];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfAVectorInAConditionalTrueArmIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  logic c;\n"
      "  logic y;\n"
      "  assign y = c ? v[0] : 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SelectElaboration, ScalarBitSelectInAConditionalTrueArmIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s;\n"
      "  logic c;\n"
      "  logic y;\n"
      "  assign y = c ? s[0] : 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
}

TEST(SelectElaboration, IndexedPartSelectWidthInAConcatenationIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [8:0] y;\n"
      "  assign y = {data[0+:w], 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 5, "11.5.1"));
}

TEST(PackedRangeSelect,
     SelectInAGenerateBlockUsesTheBlockParameterDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam logic [2:17] P = 16'h0001;\n"
      "      localparam Q = P[17];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->is_resolved);
  EXPECT_EQ(q->resolved_value, 1);
}

TEST(SelectElaboration, SelectOfATypedefOrPackedStructNetAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef logic [31:0] addressT;\n"
      "  wire addressT w1;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "  nettype logic [7:0] byte_n;\n"
      "  byte_n nb;\n"
      "  wire s;\n"
      "  wire y1, y2, y3, y4;\n"
      "  assign y1 = w1[0];\n"
      "  assign y2 = memsig[3];\n"
      "  assign y4 = nb[0];\n"
      "  assign y3 = s[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            12, "11.5.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}
