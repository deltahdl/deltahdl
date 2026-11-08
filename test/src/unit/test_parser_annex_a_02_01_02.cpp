#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(PortDeclParsing, InoutDeclWithNetPortType) {
  auto r = Parse("module m(inout wire [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "bus");
}

TEST(PortDeclParsing, InoutDeclListOfPortIdentifiers) {
  auto r = Parse("module m(inout wire a, b, c); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 3u);
  for (size_t i = 0; i < 3; ++i)
    EXPECT_EQ(r.cu->modules[0]->ports[i].direction, Direction::kInout);
}

TEST(PortDeclParsing, InputDeclWithNetPortType) {
  auto r = Parse("module m(input wire [3:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.name, "d");
}

TEST(PortDeclParsing, InputDeclWithVariablePortType) {
  auto r = Parse("module m(input logic [7:0] data); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.name, "data");
}

TEST(PortDeclParsing, InputDeclWithExplicitVarKeyword) {
  auto r = Parse("module m(input var logic [7:0] data); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_TRUE(port.has_explicit_var);
}

TEST(PortDeclParsing, OutputDeclWithNetPortType) {
  auto r = Parse("module m(output wire [7:0] q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.name, "q");
}

TEST(PortDeclParsing, OutputDeclWithVariablePortType) {
  auto r = Parse("module m(output logic [3:0] q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.name, "q");
}

TEST(PortDeclParsing, OutputDeclWithDefault) {
  auto r = Parse("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(PortDeclParsing, InterfacePortBareIdentifier) {
  auto r = Parse(
      "interface bus_if; logic clk; endinterface\n"
      "module m(bus_if b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.name, "b");
}

TEST(PortDeclParsing, InterfacePortWithModport) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic clk;\n"
      "  modport mp(input clk);\n"
      "endinterface\n"
      "module m(bus_if.mp b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.name, "b");
  EXPECT_EQ(port.data_type.modport_name, "mp");
}

TEST(PortDeclParsing, InterfacePortWithInterfaceKeyword) {
  auto r = Parse(
      "interface bus_if; logic clk; endinterface\n"
      "module m(interface b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_EQ(port.name, "b");
}

TEST(PortDeclParsing, RefDeclWithVariablePortType) {
  auto r = Parse("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_EQ(port.name, "d");
}

TEST(PortDeclParsing, NonAnsiInputDecl) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input wire [3:0] a;\n"
      "  input logic b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kInput);
}

TEST(PortDeclParsing, NonAnsiOutputDecl) {
  auto r = Parse(
      "module m(q);\n"
      "  output logic [7:0] q;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(PortDeclParsing, NonAnsiInoutDecl) {
  auto r = Parse(
      "module m(bus);\n"
      "  inout wire [3:0] bus;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(PortDeclParsing, NonAnsiRefDecl) {
  auto r = Parse(
      "module m(a, b);\n"
      "  ref logic a, b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kRef);
}

TEST(PortDeclParsing, NonAnsiImplicitTypeWithSeveralPackedDims) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [3:0][1:0] a;\n"
      "  output [1:0][7:0][2:0] b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.extra_packed_dims.size(), 1u);
  EXPECT_EQ(ports[1].data_type.extra_packed_dims.size(), 2u);
  EXPECT_TRUE(ports[0].data_type.is_net);
}

TEST(PortDeclParsing, NonAnsiOutputVariablePortInitializer) {
  auto r = Parse(
      "module m(q, r, s);\n"
      "  output logic q = 1'b0;\n"
      "  output var int r = 5, s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_NE(ports[0].default_value, nullptr);
  EXPECT_NE(ports[1].default_value, nullptr);
  EXPECT_EQ(ports[2].default_value, nullptr);
}

TEST(PortDeclParsing, BodyPortDeclarationOfAPackageScopedType) {
  auto r = Parse(
      "package pk;\n"
      "  typedef logic [3:0] t;\n"
      "endpackage\n"
      "module m(a, b);\n"
      "  input pk::t a;\n"
      "  output var pk::t b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  for (const auto& port : ports) {
    EXPECT_EQ(port.data_type.scope_name, "pk");
    EXPECT_EQ(port.data_type.type_name, "t");
  }
  EXPECT_TRUE(ports[1].has_explicit_var);
}

TEST(PortDeclParsing, ErrorInputMissingIdentifier) {
  auto r = Parse("module m(input wire); endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ')'", 1, "23.2.2.2"));
}

TEST(PortDeclParsing, ErrorRefMissingIdentifier) {
  auto r = Parse("module m(ref logic); endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ')'", 1, "23.2.2.2"));
}

TEST(PortDeclParsing, VarPortsOfATypeReference) {
  auto r = Parse(
      "module m(input int x, input var type(x) a);\n"
      "endmodule\n"
      "module n(c);\n"
      "  int x;\n"
      "  input var type(x) c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[1].data_type.type_ref_expr, nullptr);
  ASSERT_EQ(r.cu->modules[1]->ports.size(), 1u);
  EXPECT_NE(r.cu->modules[1]->ports[0].data_type.type_ref_expr, nullptr);
}

TEST(PortDeclParsing, PortOfATypeReferenceWithNeitherKeywordIsReported) {
  auto r = Parse(
      "module m(input int x, input type(x) e);\n"
      "endmodule\n"
      "module n(c);\n"
      "  int x;\n"
      "  input type(x) c;\n"
      "endmodule\n");
  for (uint32_t line : {1U, 5U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "type_reference in a port declaration must be "
                              "preceded by the 'var' keyword or a net type "
                              "keyword",
                              line, "6.23"));
  }
}

}  // namespace
