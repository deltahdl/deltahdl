
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1: A port declared as input (output) but used as output (input) or inout
//     may be coerced to inout ---

TEST(PortCoercionElaboration, InputPortDrivenInternallyDoesNotError) {
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
}

TEST(PortCoercionElaboration, OutputPortWithExternalDriverDoesNotError) {
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
}

TEST(PortCoercionElaboration, InputPortUsedAsInoutDoesNotError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire data);\n"
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
}

// --- R2: If not coerced to inout, a warning shall be issued ---

TEST(PortCoercionElaboration, InputPortDrivenInternallyWarns) {
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

TEST(PortCoercionElaboration, OutputPortWithExternalDriverWarns) {
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

TEST(PortCoercionElaboration, InputPortUsedAsInoutWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire data);\n"
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
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// --- Negative cases: correct usage produces no coercion warning ---

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

}  // namespace
