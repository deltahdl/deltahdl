
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SignedValuesViaPortsSimulation,
     SignedInputDoesNotSignExtendInChild) {

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

TEST(SignedValuesViaPortsSimulation,
     NarrowerSignedExpressionSignExtendedOnPortAssignment) {

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

}
