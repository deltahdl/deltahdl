

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ModuleDeclaration, EmptyPortListParens) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// --- inout_declaration: inout net_port_type list_of_port_identifiers ---

TEST(PortDeclParsing, InoutImplicitNetType) {
  auto r = Parse("module m(inout a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "a");
}

TEST(PortDeclParsing, InoutWirePackedDims) {
  auto r = Parse("module m(inout wire [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "bus");
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(PortDeclParsing, InoutTriNetType) {
  auto r = Parse("module m(inout tri [3:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "d");
}

// --- input_declaration: input net_port_type / variable_port_type ---

TEST(PortDeclParsing, InputImplicitNetType) {
  auto r = Parse("module m(input a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.name, "a");
}

TEST(PortDeclParsing, InputWireNetType) {
  auto r = Parse("module m(input wire [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.name, "d");
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(PortDeclParsing, InputVariablePortTypeLogic) {
  auto r = Parse("module m(input logic [15:0] data); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
}

TEST(PortDeclParsing, InputVariablePortTypeVar) {
  auto r = Parse("module m(input var logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.name, "d");
}

TEST(PortDeclParsing, InputIntegerAtomType) {
  auto r = Parse("module m(input int idx); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInt);
}

// --- output_declaration: output net_port_type / variable_port_type ---

TEST(PortDeclParsing, OutputImplicitNetType) {
  auto r = Parse("module m(output b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.name, "b");
}

TEST(PortDeclParsing, OutputRegNetType) {
  auto r = Parse("module m(output reg [3:0] q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kReg);
}

TEST(PortDeclParsing, OutputVariablePortTypeLogic) {
  auto r = Parse("module m(output logic [7:0] result); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.name, "result");
}

TEST(PortDeclParsing, OutputVariablePortTypeVar) {
  auto r = Parse("module m(output var logic q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.name, "q");
}

TEST(PortDeclParsing, OutputWithDefaultValue) {
  auto r = Parse("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

// --- interface_port_declaration ---

TEST(PortDeclParsing, InterfacePortBareKeyword) {
  auto r = Parse("module m(interface bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_EQ(port.name, "bus");
}

TEST(PortDeclParsing, InterfacePortWithModport) {
  auto r = Parse("module m(interface.master bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_EQ(port.data_type.modport_name, "master");
  EXPECT_EQ(port.name, "bus");
}

TEST(PortDeclParsing, NamedInterfacePortWithModport) {
  auto r = Parse("module m(bus_if.slave s); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.modport_name, "slave");
  EXPECT_EQ(port.name, "s");
}

// --- ref_declaration: ref variable_port_type list_of_variable_identifiers ---

TEST(PortDeclParsing, RefLogicPort) {
  auto r = Parse("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.name, "d");
}

TEST(PortDeclParsing, RefIntPort) {
  auto r = Parse("module m(ref int arr); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInt);
}

TEST(PortDeclParsing, RefWithUnpackedDims) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

// --- Edge cases ---

TEST(PortDeclParsing, AllFourDirections) {
  auto r = Parse(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kRef);
}

TEST(PortDeclParsing, InputSignedImplicitType) {
  auto r = Parse("module m(input signed [7:0] s); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.name, "s");
}

TEST(PortDeclParsing, OutputByteType) {
  auto r = Parse("module m(output byte b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kByte);
}

TEST(PortDeclParsing, InputLongintType) {
  auto r = Parse("module m(input longint addr); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLongint);
}

TEST(PortDeclParsing, OutputShortintType) {
  auto r = Parse("module m(output shortint val); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kShortint);
}

TEST(PortDeclParsing, InputWithUnpackedDims) {
  auto r = Parse("module m(input logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

// --- Explicitly named ANSI ports ---

TEST(PortDeclParsing, ExplicitlyNamedPortWithExpression) {
  auto r = Parse("module m(output .P1(r[3:0])); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.name, "P1");
  EXPECT_NE(port.port_expr, nullptr);
}

TEST(PortDeclParsing, ExplicitlyNamedPortEmptyExpression) {
  auto r = Parse("module m(output .P1()); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.name, "P1");
  EXPECT_EQ(port.port_expr, nullptr);
}

TEST(PortDeclParsing, ExplicitlyNamedPortNoDirection) {
  auto r = Parse("module m(.P1(x)); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kNone);
  EXPECT_EQ(port.name, "P1");
  EXPECT_NE(port.port_expr, nullptr);
}

TEST(PortDeclParsing, MultipleExplicitlyNamedPorts) {
  auto r = Parse(
      "module mymod (\n"
      "  output .P1(r[3:0]),\n"
      "  output .P2(r[7:4]),\n"
      "  ref    .Y(x),\n"
      "  input  R);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "P1");
  EXPECT_NE(r.cu->modules[0]->ports[0].port_expr, nullptr);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "P2");
  EXPECT_NE(r.cu->modules[0]->ports[1].port_expr, nullptr);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "Y");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "R");
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kInput);
}

// --- Generic interface ports ---

TEST(PortDeclParsing, GenericInterfacePortMultiple) {
  auto r = Parse("module cpuMod(interface d, interface j); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "d");
  EXPECT_TRUE(r.cu->modules[0]->ports[1].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "j");
}

// --- LRM examples ---

TEST(PortDeclParsing, LrmExampleAnsiTestModule) {
  auto r = Parse(
      "module test (\n"
      "  input [7:0] a,\n"
      "  input signed [7:0] b, c, d,\n"
      "  output [7:0] e,\n"
      "  output var signed [7:0] f, g,\n"
      "  output signed [7:0] h);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 8u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[7].name, "h");
  EXPECT_EQ(r.cu->modules[0]->ports[7].direction, Direction::kOutput);
}

// --- Additional Syntax 23-4 coverage ---

TEST(PortDeclParsing, InterfacePortWithUnpackedDims) {
  auto r = Parse("module m(interface bus [2]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(PortDeclParsing, InputWithDefaultValue) {
  auto r = Parse("module m(input logic x = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.default_value, nullptr);
}

// --- Error conditions ---

TEST(PortDeclParsing, ErrorMissingPortName) {
  auto r = Parse("module m(input logic); endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(PortDeclParsing, ErrorMissingCloseParen) {
  auto r = Parse("module m(input logic a; endmodule");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
