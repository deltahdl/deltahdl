// §23.2.2.2: ANSI style list of port declarations

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Module with both parameters and ports
TEST(SourceText, ParamsAndPorts) {
  auto r = ParseWithPreprocessor(
      "module m #(parameter int W = 8)(input logic [W-1:0] data,\n"
      "                                 output logic valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "W");
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "valid");
}

TEST(Parser, ModuleWithPorts) {
  auto r = ParseWithPreprocessor(
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

// Module with ANSI header (list_of_port_declarations).
TEST(SourceText, ModuleAnsiHeader) {
  auto r = ParseWithPreprocessor(
      "module m(input logic a, output logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// port_declaration: all 4 directions (port_direction ::=
// input|output|inout|ref)
TEST(SourceText, PortDirectionAllFour) {
  auto r = ParseWithPreprocessor(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

// net_port_header: [port_direction] net_port_type — inout wire
TEST(SourceText, NetPortHeader) {
  auto r =
      ParseWithPreprocessor("module m(inout wire [7:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
}

// variable_port_header: [port_direction] variable_port_type — input logic
TEST(SourceText, VariablePortHeader) {
  auto r =
      ParseWithPreprocessor("module m(input logic [3:0] sel); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "sel");
}

TEST(ParserAnnexA, A1ModulePortDirections) {
  auto r = ParseWithPreprocessor(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  const Direction kExpected[] = {Direction::kInput, Direction::kOutput,
                                 Direction::kInout, Direction::kRef};
  for (size_t i = 0; i < 4; i++) {
    EXPECT_EQ(ports[i].direction, kExpected[i]);
  }
}

TEST(ParserA212, InputVariablePortTypeVar) {
  // variable_port_type ::= var_data_type
  // var_data_type ::= var data_type_or_implicit
  auto r = ParseWithPreprocessor("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

// --- output_declaration ---
// output net_port_type list_of_port_identifiers
// | output variable_port_type list_of_variable_port_identifiers
TEST(ParserA212, OutputNetPortType) {
  auto r = ParseWithPreprocessor("module m(output wire q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ParserA212, OutputVariablePortTypeReg) {
  auto r = ParseWithPreprocessor("module m(output reg q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

// --- ref_declaration ---
// ref variable_port_type list_of_variable_identifiers
TEST(ParserA212, RefDeclaration) {
  auto r = ParseWithPreprocessor("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
}

// --- net_port_type ---
// [ net_type ] data_type_or_implicit | interconnect implicit_data_type
TEST(ParserA212, NetPortTypeTriType) {
  auto r = ParseWithPreprocessor("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "bus");
}

// --- variable_port_type ---
// var_data_type ::= data_type | var data_type_or_implicit
TEST(ParserA212, VarDataTypeExplicit) {
  // var_data_type: data_type (integer_vector_type)
  auto r = ParseWithPreprocessor(
      "module m(input logic signed [15:0] val); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA212, VarDataTypeInt) {
  // var_data_type: data_type (integer_atom_type)
  auto r = ParseWithPreprocessor("module m(input int count); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

// --- list_of_port_identifiers ---
// port_identifier { unpacked_dimension }
//     { , port_identifier { unpacked_dimension } }
TEST(ParserA23, ListOfPortIdentifiersSingle) {
  auto r = ParseWithPreprocessor("module m(inout wire a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(ParserA23, ListOfPortIdentifiersWithUnpackedDim) {
  auto r = ParseWithPreprocessor("module m(inout logic a [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

TEST(ParserA23, ListOfVariableIdentifiersMultipleAnsi) {
  auto r = ParseWithPreprocessor(
      "module m(input logic a, input logic b, input logic c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

}  // namespace
