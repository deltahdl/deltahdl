#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PortCoercionElaboration, InputDrivenInsideModuleWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration, OutputWithExternalDriverWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire b);\n"
      "  assign b = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  assign y = 1'b0;\n"
      "  child u(.b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration, CorrectDirectionsNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x, y;\n"
      "  child u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration, InoutPortNeedsNoCoercion) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire data);\n"
      "  assign data = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire bus;\n"
      "  assign bus = 1'b0;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration, VectorInputDrivenInsideModuleWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire [7:0] a);\n"
      "  assign a = 8'hFF;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration, PositionalConnectionOutputWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire b);\n"
      "  assign b = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  assign y = 1'b0;\n"
      "  child u(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration, NonAnsiInputPortDrivenWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a);\n"
      "  input a;\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(PortCoercionElaboration,
     NonAnsiInputPortRedeclaredAsVariableDrivenErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(a);\n"
      "  input a;\n"
      "  reg a;\n"
      "  initial a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is declared as an input port and cannot be the "
                            "target of an assignment",
                            4, "23.3.3.2"));
}

TEST(PortCoercionElaboration, NonAnsiVarInputPortDrivenErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(a);\n"
      "  input var a;\n"
      "  initial a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is declared as an input port and cannot be the "
                            "target of an assignment",
                            3, "23.3.3.2"));
}

}  // namespace
