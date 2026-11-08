#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SingleSourceNetsElaboration,
     InternalUwireInputPortConnectedToExternalVariableWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     InternalUwireOutputPortConnectedToExternalVariableWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output uwire b);\n"
      "  assign b = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic y;\n"
      "  child u(.b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     ExternalUwireNetConnectedToInternalVariableInputPortWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     ExternalUwireNetConnectedToInternalVariableOutputPortWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic b);\n"
      "  assign b = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  uwire y;\n"
      "  assign y = 1'b1;\n"
      "  child u(.b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, UwireInputPortConnectedToExpressionWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.a(x + 8'd1));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, UwireInputPortConnectedToLiteralWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u(.a(8'hFF));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     InternalUwirePortConnectedToExternalWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     InternalUwirePortConnectedToExternalUwireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     ExternalWireConnectedToInternalWirePortNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     ExternalWireConnectedToInternalUwireOutputPortNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output uwire b);\n"
      "  assign b = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  child u(.b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     ExternalUwireNetConnectedToInternalWirePortNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, UwirePortLeftUnconnectedNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a, input wire b);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.b(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, UwireInoutPortConnectedToWireNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, UwirePortConnectedToTriNetNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri t;\n"
      "  child u(.a(t));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration,
     UwirePortPositionalConnectionToVariableWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, UwireInoutKeptApartForSdfAnnotateWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire p);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire n;\n"
      "  child c(.p(n));\n"
      "  initial $sdf_annotate(\"t.sdf\", top);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "uwire net on port 'p' of instance 'c' is not merged into a single net",
      5, "23.3.3.6"));
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(SingleSourceNetsElaboration,
     ExternalUwireOnAnInoutKeptApartForSdfAnnotateWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire p);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire n;\n"
      "  child c(.p(n));\n"
      "  initial $sdf_annotate(\"t.sdf\", top);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "uwire net on port 'p' of instance 'c' is not merged into a single net",
      5, "23.3.3.6"));
}

TEST(SingleSourceNetsElaboration, UwireInoutMergedWithoutSdfAnnotateNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire p);\n"
      "endmodule\n"
      "module top;\n"
      "  uwire n;\n"
      "  child c(.p(n));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, ACallElaboratedLaterStillDrawsTheWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout uwire p);\n"
      "endmodule\n"
      "module mid;\n"
      "  uwire n;\n"
      "  child c(.p(n));\n"
      "endmodule\n"
      "module tb;\n"
      "  initial $sdf_annotate(\"t.sdf\");\n"
      "endmodule\n"
      "module top;\n"
      "  mid m();\n"
      "  tb t();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "uwire net on port 'p' of instance 'c' is not merged into a single net",
      5, "23.3.3.6"));
}

TEST(SingleSourceNetsElaboration, UwireInputInADesignThatAnnotatesNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child c(.a(w));\n"
      "  initial $sdf_annotate(\"t.sdf\", top);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SingleSourceNetsElaboration, ACoercedUwireInputKeptApartWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input uwire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child c(.a(w));\n"
      "  initial $sdf_annotate(\"t.sdf\", top);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "uwire net on port 'a' of instance 'c' is not merged into a single net",
      6, "23.3.3.6"));
}

}  // namespace
