
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- R1: The sign attribute shall not cross hierarchy ---

TEST(SignedValuesViaPortsSimulation,
     SignedInputDoesNotSignExtendInChild) {
  // Parent's signed [7:0] x = -1 (8'hFF) connects to child's unsigned [7:0] a.
  // Inside child, a is unsigned, so widening to [15:0] zero-extends → 0x00FF.
  EXPECT_EQ(RunAndGet(
      "module child(input logic [7:0] a, output logic [15:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  logic [15:0] result;\n"
      "  child u(.a(x), .b(result));\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "result"), 0x00FFu);
}

TEST(SignedValuesViaPortsSimulation,
     BothSidesSignedAllowsSignExtensionInChild) {
  // Parent's signed [7:0] x = -1 connects to child's signed [7:0] a.
  // Inside child, a is signed, so widening to [15:0] sign-extends → 0xFFFF.
  EXPECT_EQ(RunAndGet(
      "module child(input logic signed [7:0] a, output logic [15:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  logic [15:0] result;\n"
      "  child u(.a(x), .b(result));\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "result"), 0xFFFFu);
}

TEST(SignedValuesViaPortsSimulation,
     UnsignedInputToSignedPortInterpretedAsSigned) {
  // Parent's unsigned [7:0] x = 8'hFF connects to child's signed [7:0] a.
  // Inside child, a is signed per child's own declaration, so widening
  // to [15:0] sign-extends → 0xFFFF.
  EXPECT_EQ(RunAndGet(
      "module child(input logic signed [7:0] a, output logic [15:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [15:0] result;\n"
      "  child u(.a(x), .b(result));\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n",
      "result"), 0xFFFFu);
}

TEST(SignedValuesViaPortsSimulation,
     SignedOutputBitPatternPreserved) {
  // Child's signed output = -1 (8'hFF) connects to parent's unsigned [7:0].
  // Same width, so bit pattern 8'hFF is preserved.
  EXPECT_EQ(RunAndGet(
      "module child(output logic signed [7:0] o);\n"
      "  assign o = -1;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  child u(.o(result));\n"
      "endmodule\n",
      "result"), 0xFFu);
}

// --- R2: Port expressions follow assignment rules ---

TEST(SignedValuesViaPortsSimulation,
     NarrowerSignedExpressionSignExtendedOnPortAssignment) {
  // Parent's signed [3:0] x = -1 (4'hF) connects to child's unsigned [7:0] a.
  // The expression x is evaluated as signed 4-bit in the parent scope, then
  // assigned to the 8-bit port per assignment rules: sign-extends to 8'hFF.
  EXPECT_EQ(RunAndGet(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic signed [3:0] x;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(x), .b(result));\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "result"), 0xFFu);
}

}  // namespace
