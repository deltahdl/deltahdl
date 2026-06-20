
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SignedValuesViaPortsSimulation, SignedInputDoesNotSignExtendInChild) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [15:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module t;\n"
                "  logic signed [7:0] x;\n"
                "  logic [15:0] result;\n"
                "  child u(.a(x), .b(result));\n"
                "  initial x = -1;\n"
                "endmodule\n",
                "result"),
      0x00FFu);
}

TEST(SignedValuesViaPortsSimulation,
     BothSidesSignedAllowsSignExtensionInChild) {
  EXPECT_EQ(
      RunAndGet(
          "module child(input logic signed [7:0] a, output logic [15:0] b);\n"
          "  assign b = a;\n"
          "endmodule\n"
          "module t;\n"
          "  logic signed [7:0] x;\n"
          "  logic [15:0] result;\n"
          "  child u(.a(x), .b(result));\n"
          "  initial x = -1;\n"
          "endmodule\n",
          "result"),
      0xFFFFu);
}

TEST(SignedValuesViaPortsSimulation,
     UnsignedInputToSignedPortInterpretedAsSigned) {
  EXPECT_EQ(
      RunAndGet(
          "module child(input logic signed [7:0] a, output logic [15:0] b);\n"
          "  assign b = a;\n"
          "endmodule\n"
          "module t;\n"
          "  logic [7:0] x;\n"
          "  logic [15:0] result;\n"
          "  child u(.a(x), .b(result));\n"
          "  initial x = 8'hFF;\n"
          "endmodule\n",
          "result"),
      0xFFFFu);
}

TEST(SignedValuesViaPortsSimulation, SignedOutputBitPatternPreserved) {
  EXPECT_EQ(RunAndGet("module child(output logic signed [7:0] o);\n"
                      "  assign o = -1;\n"
                      "endmodule\n"
                      "module t;\n"
                      "  logic [7:0] result;\n"
                      "  child u(.o(result));\n"
                      "endmodule\n",
                      "result"),
            0xFFu);
}

TEST(SignedValuesViaPortsSimulation,
     NarrowerSignedExpressionSignExtendedOnPortAssignment) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module t;\n"
                "  logic signed [3:0] x;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(x), .b(result));\n"
                "  initial x = -1;\n"
                "endmodule\n",
                "result"),
      0xFFu);
}

// An arbitrary expression on a port connection is evaluated and then sized to
// the port width using assignment rules. Here p + 1 produces an 8-bit 0xFF,
// which is truncated to the 4-bit input port, so only the low nibble survives.
TEST(SignedValuesViaPortsSimulation,
     ExpressionOnPortTruncatedToPortWidthLikeAssignment) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [3:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module t;\n"
                "  logic [7:0] p;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(p + 8'd1), .b(result));\n"
                "  initial p = 8'hFE;\n"
                "endmodule\n",
                "result"),
      0x0Fu);
}

// Sign must not cross hierarchy on the output path either. The child drives a
// signed output, but the receiving net is unsigned; widening that receiver
// must zero-extend (per the receiver's own declaration), not sign-extend.
TEST(SignedValuesViaPortsSimulation,
     SignedOutputToUnsignedReceiverDoesNotSignExtend) {
  EXPECT_EQ(RunAndGet("module child(output logic signed [7:0] o);\n"
                      "  assign o = -1;\n"
                      "endmodule\n"
                      "module t;\n"
                      "  logic [7:0] y;\n"
                      "  logic [15:0] result;\n"
                      "  child u(.o(y));\n"
                      "  assign result = y;\n"
                      "endmodule\n",
                      "result"),
            0x00FFu);
}

// With the signed keyword at both levels, the signed type does cross hierarchy
// on the output path: a signed output feeding a signed receiver sign-extends
// when that receiver is widened.
TEST(SignedValuesViaPortsSimulation, SignedOutputToSignedReceiverSignExtends) {
  EXPECT_EQ(RunAndGet("module child(output logic signed [7:0] o);\n"
                      "  assign o = -1;\n"
                      "endmodule\n"
                      "module t;\n"
                      "  logic signed [7:0] y;\n"
                      "  logic [15:0] result;\n"
                      "  child u(.o(y));\n"
                      "  assign result = y;\n"
                      "endmodule\n",
                      "result"),
            0xFFFFu);
}

// A narrow unsigned expression on a port connection is sized to the wider port
// using assignment rules, which for an unsigned source means zero-extension.
TEST(SignedValuesViaPortsSimulation,
     UnsignedNarrowExpressionZeroExtendedOnPortAssignment) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module t;\n"
                "  logic [3:0] x;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(x), .b(result));\n"
                "  initial x = 4'hF;\n"
                "endmodule\n",
                "result"),
      0x0Fu);
}

}  // namespace
