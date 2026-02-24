// §23.2.2.2: ANSI style list of port declarations

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// Module with ANSI header (list_of_port_declarations).
TEST(SourceText, ModuleAnsiHeader) {
  auto r = Parse("module m(input logic a, output logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// list_of_port_declarations: empty ()
TEST(SourceText, EmptyPortList) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

// port_declaration: all 4 directions (port_direction ::=
// input|output|inout|ref)
TEST(SourceText, PortDirectionAllFour) {
  auto r = Parse(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

// net_port_header: [port_direction] net_port_type — inout wire
TEST(SourceText, NetPortHeader) {
  auto r = Parse("module m(inout wire [7:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
}

// variable_port_header: [port_direction] variable_port_type — input logic
TEST(SourceText, VariablePortHeader) {
  auto r = Parse("module m(input logic [3:0] sel); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "sel");
}

TEST(ParserAnnexA, A1ModulePortDirections) {
  auto r = Parse(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  const Direction kExpected[] = {Direction::kInput, Direction::kOutput,
                                 Direction::kInout, Direction::kRef};
  for (size_t i = 0; i < 4; i++) {
    EXPECT_EQ(ports[i].direction, kExpected[i]);
  }
}

// =============================================================================
// A.2.1.2 Port declarations
// =============================================================================
// --- inout_declaration ---
// inout net_port_type list_of_port_identifiers
TEST(ParserA212, InoutWireNetType) {
  auto r = Parse("module m(inout wire a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "a");
}

TEST(ParserA212, InoutPackedDim) {
  auto r = Parse("module m(inout [7:0] a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA212, InputVariablePortTypeVar) {
  // variable_port_type ::= var_data_type
  // var_data_type ::= var data_type_or_implicit
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

// --- output_declaration ---
// output net_port_type list_of_port_identifiers
// | output variable_port_type list_of_variable_port_identifiers
TEST(ParserA212, OutputNetPortType) {
  auto r = Parse("module m(output wire q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ParserA212, OutputVariablePortTypeReg) {
  auto r = Parse("module m(output reg q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

// --- ref_declaration ---
// ref variable_port_type list_of_variable_identifiers
TEST(ParserA212, RefDeclaration) {
  auto r = Parse("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
}

// --- net_port_type ---
// [ net_type ] data_type_or_implicit | interconnect implicit_data_type
TEST(ParserA212, NetPortTypeTriType) {
  auto r = Parse("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "bus");
}

// --- variable_port_type ---
// var_data_type ::= data_type | var data_type_or_implicit
TEST(ParserA212, VarDataTypeExplicit) {
  // var_data_type: data_type (integer_vector_type)
  auto r = Parse("module m(input logic signed [15:0] val); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA212, VarDataTypeInt) {
  // var_data_type: data_type (integer_atom_type)
  auto r = Parse("module m(input int count); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

}  // namespace
