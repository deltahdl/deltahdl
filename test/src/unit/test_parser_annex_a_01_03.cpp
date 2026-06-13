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

TEST(ModuleParametersAndPorts, InputVariablePortTypeVar) {
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
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

// --- parameter_port_list (prod 1) ---

// A leading #( ... ) introduces a parameter_port_list ahead of the port list.
TEST(ModuleParametersAndPorts, ParameterPortList) {
  auto r = Parse(
      "module m #(parameter int W = 8) (input logic a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_param_port_list);
  ASSERT_EQ(mod->params.size(), 1u);
  EXPECT_EQ(mod->params[0].first, "W");
  EXPECT_NE(mod->params[0].second, nullptr);
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "a");
}

// The #( ) alternative carries an empty parameter_port_list.
TEST(ModuleParametersAndPorts, ParameterPortListEmpty) {
  auto r = Parse("module m #() (); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_param_port_list);
  EXPECT_TRUE(mod->params.empty());
}

// --- parameter_port_declaration (prod 2) ---

// local_parameter_declaration alternative inside a parameter_port_list.
TEST(ModuleParametersAndPorts, ParameterPortDeclLocalparam) {
  auto r = Parse("module m #(parameter P = 1, localparam Q = 2) (); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 2u);
  EXPECT_EQ(mod->params[0].first, "P");
  EXPECT_EQ(mod->params[1].first, "Q");
  EXPECT_EQ(mod->localparam_port_names.count("Q"), 1u);
  EXPECT_EQ(mod->localparam_port_names.count("P"), 0u);
}

// type_parameter_declaration alternative inside a parameter_port_list.
TEST(ModuleParametersAndPorts, ParameterPortDeclTypeParameter) {
  auto r = Parse("module m #(parameter type T = int) (); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->type_param_names.count("T"), 1u);
}

// data_type list_of_param_assignments alternative (no parameter keyword).
TEST(ModuleParametersAndPorts, ParameterPortDeclDataType) {
  auto r = Parse("module m #(int W = 8) (); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 1u);
  EXPECT_EQ(mod->params[0].first, "W");
  ASSERT_EQ(mod->param_types.size(), 1u);
  EXPECT_EQ(mod->param_types[0].kind, DataTypeKind::kInt);
}

// --- list_of_ports / port / port_expression / port_reference (prods 3,6,7,8) ---

// A non-ANSI list_of_ports is a parenthesized comma list of bare
// port_reference port identifiers.
TEST(ModuleParametersAndPorts, NonAnsiListOfPorts) {
  auto r = Parse("module m (a, b, c); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[2].name, "c");
}

// port_reference allows a constant_select on the port identifier.
TEST(ModuleParametersAndPorts, PortReferenceWithSelect) {
  auto r = Parse("module m (a[0], b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "a");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kSelect);
}

// port_expression may be a braced concatenation of port_references.
TEST(ModuleParametersAndPorts, PortExpressionConcatenation) {
  auto r = Parse("module m ({a, b}, c); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_NE(mod->ports[0].port_expr, nullptr);
}

// port's explicit ". port_identifier ( port_expression )" form names the
// external port and binds it to an internal expression.
TEST(ModuleParametersAndPorts, PortExplicitlyNamed) {
  auto r = Parse("module m (.x(a), .y(b)); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_TRUE(mod->ports[0].is_explicit_named);
  EXPECT_EQ(mod->ports[0].name, "x");
  EXPECT_NE(mod->ports[0].port_expr, nullptr);
}

// --- port_declaration (prod 5) ---

// In the non-ANSI style, directions are supplied by body port_declarations
// that bind back to the names listed in the header.
TEST(ModuleParametersAndPorts, NonAnsiPortDeclarations) {
  auto r = Parse(
      "module m (a, b, c);\n"
      "  input  a;\n"
      "  output b;\n"
      "  inout  c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[2].direction, Direction::kInout);
}

// A non-ANSI body port_declaration may be preceded by attribute_instances.
TEST(ModuleParametersAndPorts, NonAnsiPortDeclarationsWithAttributes) {
  auto r = Parse(
      "module m (a, b);\n"
      "  (* keep *) input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
}

// --- interface_port_header (prod 12, interface-keyword form) ---

// The generic "interface [ . modport_identifier ]" port header form.
TEST(ModuleParametersAndPorts, GenericInterfacePortHeader) {
  auto r = Parse("module m (interface.master bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_TRUE(mod->ports[0].is_interface_port);
  EXPECT_EQ(mod->ports[0].name, "bus");
}

// --- ansi_port_declaration (prod 13, explicit ".port(expr)" form) ---

// The "[ port_direction ] . port_identifier ( [ expression ] )" ANSI form.
TEST(ModuleParametersAndPorts, AnsiExplicitlyNamedPort) {
  auto r = Parse("module m (input .x(a)); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_TRUE(mod->ports[0].is_explicit_named);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "x");
  EXPECT_NE(mod->ports[0].port_expr, nullptr);
}

// --- edge cases ---

// ansi_port_declaration permits a trailing "= constant_expression" default.
TEST(ModuleParametersAndPorts, AnsiPortDefaultValue) {
  auto r = Parse("module m(input int x = 5); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_NE(mod->ports[0].default_value, nullptr);
}

// A port may be empty: a "port" is an optional port_expression, so an omitted
// entry in a non-ANSI list_of_ports is a legal unconnected position.
TEST(ModuleParametersAndPorts, NonAnsiEmptyPort) {
  auto r = Parse("module m (a, , b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->is_non_ansi_ports);
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_TRUE(mod->ports[1].name.empty());
  EXPECT_EQ(mod->ports[1].port_expr, nullptr);
  EXPECT_EQ(mod->ports[2].name, "b");
}

// port_reference's constant_select may be a part-select range, not just an
// index.
TEST(ModuleParametersAndPorts, PortReferenceRangeSelect) {
  auto r = Parse("module m (a[3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kSelect);
  EXPECT_NE(mod->ports[0].port_expr->index_end, nullptr);
}

// The generic interface port header may omit the ". modport_identifier" part.
TEST(ModuleParametersAndPorts, GenericInterfacePortNoModport) {
  auto r = Parse("module m (interface bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_TRUE(mod->ports[0].is_interface_port);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_TRUE(mod->ports[0].data_type.modport_name.empty());
}

// Each ansi_port_declaration in a list_of_port_declarations may be preceded by
// attribute_instances.
TEST(ModuleParametersAndPorts, AnsiPortsWithAttributes) {
  auto r = Parse(
      "module m((* keep *) input logic a,\n"
      "         (* x = 1 *) output logic b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].name, "b");
}

// --- error conditions ---

// parameter_port_list requires the closing ")".
TEST(ModuleParametersAndPorts, ParameterPortListMissingCloseParen) {
  auto r = Parse("module m #(parameter int W = 8 ; endmodule");
  EXPECT_TRUE(r.has_errors);
}

// list_of_port_declarations requires the closing ")".
TEST(ModuleParametersAndPorts, PortListMissingCloseParen) {
  auto r = Parse("module m (input logic a ; endmodule");
  EXPECT_TRUE(r.has_errors);
}

// A non-ANSI body port_declaration must be terminated by ";".
TEST(ModuleParametersAndPorts, NonAnsiPortDeclMissingSemicolon) {
  auto r = Parse(
      "module m (a);\n"
      "  input a\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The explicit-named ANSI port form requires "(" after the port identifier.
TEST(ModuleParametersAndPorts, AnsiExplicitlyNamedPortMissingParen) {
  auto r = Parse("module m (input .x a); endmodule");
  EXPECT_TRUE(r.has_errors);
}

}
