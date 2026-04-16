
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1: The sign attribute shall not cross hierarchy; each side's signedness
//     comes from its own declaration ---

TEST(SignedValuesViaPortsElaboration,
     SignedSignalToUnsignedInputPortElaborates) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic signed [7:0] x;\n"
             "  logic [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(SignedValuesViaPortsElaboration,
     UnsignedSignalToSignedInputPortElaborates) {
  EXPECT_TRUE(
      ElabOk("module child(input logic signed [7:0] a,\n"
             "             output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  logic [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(SignedValuesViaPortsElaboration,
     BothSidesSignedElaborates) {
  EXPECT_TRUE(
      ElabOk("module child(input logic signed [7:0] a,\n"
             "             output logic signed [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic signed [7:0] x;\n"
             "  logic signed [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(SignedValuesViaPortsElaboration,
     PortSignednessReflectsOwnDeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic signed [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  child u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_FALSE(design->top_modules[0]->children.empty());
  auto* child_mod = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child_mod, nullptr);
  ASSERT_GE(child_mod->ports.size(), 2u);
  EXPECT_TRUE(child_mod->ports[0].is_signed);
  EXPECT_FALSE(child_mod->ports[1].is_signed);
}

TEST(SignedValuesViaPortsElaboration,
     SignedOutputToUnsignedReceiverElaborates) {
  EXPECT_TRUE(
      ElabOk("module child(output logic signed [7:0] o);\n"
             "  assign o = -1;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] y;\n"
             "  child u(.o(y));\n"
             "endmodule\n"));
}

// --- R2: Port expressions shall be typed, sized, evaluated, and assigned
//     using the same rules as an assignment ---

TEST(SignedValuesViaPortsElaboration,
     ExpressionOnPortConnectionElaborates) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic signed [3:0] x;\n"
             "  logic signed [3:0] y;\n"
             "  logic [7:0] result;\n"
             "  child u(.a(x + y), .b(result));\n"
             "endmodule\n"));
}

}  // namespace
