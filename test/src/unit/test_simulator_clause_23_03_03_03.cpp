
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- R1: input net-type port can be connected to any expression of a
//     compatible data type ---

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortReceivesValueFromParent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h42;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

// --- R2: unconnected input net-type port shall have the value 'z ---

TEST(PortConnectionRulesForNetsSimulation,
     UnconnectedInputNetPortProducesHighZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x00u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// --- R3: output net-type port can be connected to a net or variable ---

TEST(PortConnectionRulesForNetsSimulation,
     OutputNetPortDrivesParentVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire [7:0] y);\n"
      "  assign y = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.y(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

TEST(PortConnectionRulesForNetsSimulation,
     OutputNetPortDrivesParentNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire [7:0] y);\n"
      "  assign y = 8'hBE;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.y(bus));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEu);
}

// --- R4: inout net-type port can be connected to a net ---

TEST(PortConnectionRulesForNetsSimulation,
     InoutNetPortPropagatesValueToParent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

}  // namespace
