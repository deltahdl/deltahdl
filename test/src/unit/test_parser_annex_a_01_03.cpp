#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ModuleParametersAndPorts, AnsiPortDirections) {
  auto r = Parse(
      "module m (input logic a, output logic y,\n"
      "          inout wire [7:0] data, ref logic [3:0] r);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "y");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "r");
}

TEST(ModuleParametersAndPorts, AnsiPortsInputOutput) {
  auto r = Parse(
      "module m(input logic clk, input logic rst, output logic q);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[2].name, "q");
}

TEST(ModuleParametersAndPorts, AnsiPortsInout) {
  auto r = Parse(
      "module m(inout wire [7:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_EQ(mod->ports[0].name, "data");
}

TEST(ModuleParametersAndPorts, ModuleWithPortsAndAssign) {
  auto r = Parse(
      "module mux(input logic a, input logic b, input logic sel, output logic "
      "y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  struct Expected {
    Direction dir;
    const char* name;
  };
  Expected expected[] = {
      {Direction::kInput, "a"},
      {Direction::kInput, "b"},
      {Direction::kInput, "sel"},
      {Direction::kOutput, "y"},
  };
  ASSERT_EQ(mod->ports.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(mod->ports[i].name, expected[i].name) << "port " << i;
  }
}

TEST(ModuleParametersAndPorts, VariablePortHeader) {
  auto r = Parse("module m(input logic [3:0] sel); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "sel");
}

TEST(ModuleParametersAndPorts, InputVariablePortTypeVar) {
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, AnsiPortDeclarations) {
  auto r = Parse(
      "module m(\n"
      "  input  logic       clk,\n"
      "  input  logic       rst,\n"
      "  output logic [7:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 3u);
}

TEST(ModuleParametersAndPorts, AllPortDirections) {
  auto r = Parse(
      "module m(\n"
      "  input  logic a,\n"
      "  output logic b,\n"
      "  inout  wire  c,\n"
      "  ref    logic d\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

TEST(ModuleParametersAndPorts, AnsiPortUnpackedDim) {
  auto r = Parse(
      "module m(\n"
      "  input logic [7:0] data [4]\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, InterfacePortHeader) {
  auto r = Parse(
      "module m(bus_if.master bus);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, ModuleWithAnsiPortDeclarations) {
  auto r = Parse(
      "module m(input wire a, b, sel, output logic y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleParametersAndPorts, RefUnpackedDim) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, InputNetPortType) {
  auto r = Parse("module m(input wire [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, InputVariablePortTypeLogic) {
  auto r = Parse("module m(input logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, NetAsInputPort) {
  auto r = Parse(
      "module t(input wire [7:0] data_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(ports[0].data_type.is_net);
  EXPECT_EQ(ports[0].name, "data_in");
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
}

TEST(ModuleParametersAndPorts, VarAsOutputPort) {
  auto r = Parse(
      "module t(output logic [15:0] result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].direction, Direction::kOutput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[0].name, "result");
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 15u);
}

TEST(ModuleParametersAndPorts, IntegerTypesAsPortDecls) {
  auto r = Parse(
      "module m(input int a, output byte b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(ports[0].name, "a");
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(ports[1].name, "b");
}

TEST(ModuleParametersAndPorts, LongintShortintAsPorts) {
  auto r = Parse(
      "module m(input longint addr, output shortint result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(ports[0].name, "addr");
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(ports[1].name, "result");
}

TEST(ModuleParametersAndPorts, LogicPackedDimsAsPort) {
  auto r = Parse(
      "module m(input logic [7:0] data, output logic [15:0] addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[1].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[1].data_type.packed_dim_left->int_val, 15u);
}

TEST(ModuleParametersAndPorts, IntegerAsPort) {
  auto r = Parse(
      "module m(input integer idx);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
}

TEST(ModuleParametersAndPorts, VarImplicitInPort) {
  EXPECT_TRUE(
      ParseOk("module t(input var [7:0] data_in);\n"
              "endmodule\n"));
}

TEST(ModuleParametersAndPorts, ShortrealInPort) {
  EXPECT_TRUE(
      ParseOk("module m (input var shortreal in_val,\n"
              "          output var shortreal out_val);\n"
              "  assign out_val = in_val;\n"
              "endmodule\n"));
}

TEST(ModuleParametersAndPorts, InoutUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, InputUnpackedDim) {
  auto r = Parse("module m(input logic d [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ModuleParametersAndPorts, NetPortHeaderTri) {
  auto r = Parse("module m(input tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kTri);
}

TEST(ModuleParametersAndPorts, NetPortHeaderWand) {
  auto r = Parse("module m(inout wand w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kWand);
}

TEST(ModuleParametersAndPorts, NetPortHeaderWor) {
  auto r = Parse("module m(inout wor w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kWor);
}

TEST(ModuleParametersAndPorts, NetPortHeaderSupply) {
  EXPECT_TRUE(ParseOk("module m(input supply0 s0); endmodule"));
  EXPECT_TRUE(ParseOk("module m(input supply1 s1); endmodule"));
}

TEST(ModuleParametersAndPorts, NetPortHeaderUwire) {
  auto r = Parse("module m(input uwire w); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kUwire);
}

TEST(ModuleParametersAndPorts, PortDeclSignedPackedDims) {
  auto r = Parse("module m(input signed [7:0] s); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ModuleParametersAndPorts, AnsiPortMultipleUnpackedDims) {
  auto r = Parse("module m(input logic data [4][8]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->ports[0].unpacked_dims.size(), 2u);
}

}  // namespace
