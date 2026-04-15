
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1: input net-type port can be connected to any expression of a
//     compatible data type ---

TEST(PortConnectionRulesForNetsElaboration,
     InputNetPortConnectsToCompatibleExpression) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(.a(x + 8'd1));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InputNetPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  wire [7:0] w;\n"
             "  child u(.a(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InputNetPortConnectsToVariable) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] v;\n"
             "  child u(.a(v));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InputNetPortConnectsToLiteral) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u(.a(8'hFF));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InputTriPortConnectsToExpression) {
  EXPECT_TRUE(
      ElabOk("module child(input tri [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  child u(.a(x));\n"
             "endmodule\n"));
}

// --- R2: unconnected input net-type port shall have the value 'z ---

TEST(PortConnectionRulesForNetsElaboration,
     UnconnectedInputNetPortNoError) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     UnconnectedInputNetPortNamedNoError) {
  EXPECT_TRUE(
      ElabOk("module child(input wire [7:0] a, input wire b);\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.b(w));\n"
             "endmodule\n"));
}

// --- R3: output net-type port can be connected to a net or variable (or a
//     concatenation of nets or variables) of a compatible data type ---

TEST(PortConnectionRulesForNetsElaboration,
     OutputNetPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(output wire [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  wire [7:0] w;\n"
             "  child u(.y(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     OutputNetPortConnectsToVariable) {
  EXPECT_TRUE(
      ElabOk("module child(output wire [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] v;\n"
             "  child u(.y(v));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     OutputNetPortConnectsToConcatenation) {
  EXPECT_TRUE(
      ElabOk("module child(output wire [7:0] y);\n"
             "  assign y = 8'hAB;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [3:0] hi, lo;\n"
             "  child u(.y({hi, lo}));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     OutputTriPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(output tri y);\n"
             "  assign y = 1'b1;\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.y(w));\n"
             "endmodule\n"));
}

// --- R4: inout net-type port can be connected to a net (or a concatenation
//     of nets) of a compatible data type ---

TEST(PortConnectionRulesForNetsElaboration,
     InoutNetPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  wire [7:0] w;\n"
             "  child u(.a(w));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InoutNetPortConnectsToConcatenationOfNets) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  wire [3:0] hi, lo;\n"
             "  child u(.a({hi, lo}));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InoutTriPortConnectsToNet) {
  EXPECT_TRUE(
      ElabOk("module child(inout tri data);\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.data(w));\n"
             "endmodule\n"));
}

// --- R5: inout net-type port can be left unconnected ---

TEST(PortConnectionRulesForNetsElaboration,
     InoutNetPortLeftUnconnectedNoError) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesForNetsElaboration,
     InoutNetPortOmittedByNameNoError) {
  EXPECT_TRUE(
      ElabOk("module child(inout wire [7:0] a, input wire b);\n"
             "endmodule\n"
             "module top;\n"
             "  wire w;\n"
             "  child u(.b(w));\n"
             "endmodule\n"));
}

// --- R6: inout net-type port cannot be connected to a variable ---

TEST(PortConnectionRulesForNetsElaboration,
     VariableConnectedToInoutNetPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionRulesForNetsElaboration,
     VariableConnectedToInoutTriPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout tri data);\n"
      "endmodule\n"
      "module top;\n"
      "  logic v;\n"
      "  child u(.data(v));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PortConnectionRulesForNetsElaboration,
     VariableConnectedToInoutNetPortPositionalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
