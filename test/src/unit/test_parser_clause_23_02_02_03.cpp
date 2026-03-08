#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA212, InoutImplicitType) {
  auto r = Parse("module m(inout a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

TEST(ParserA212, InterfacePortParsedAsNonAnsi) {
  auto r = Parse("module m(a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kNone);
}

TEST(ParserA212, RefUnpackedDim) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserSection6, Sec6_5_NetAsInputPort) {
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

TEST(ParserSection6, Sec6_5_VarAsOutputPort) {
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

TEST(ParserSection6, ParsePortDecl_ImplicitType) {
  auto r = Parse("module m(input [3:0] a, output [7:0] b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto& ports = r.cu->modules[0]->ports;
  std::string expected_names[] = {"a", "b"};
  ASSERT_EQ(ports.size(), std::size(expected_names));
  for (size_t i = 0; i < std::size(expected_names); ++i) {
    EXPECT_EQ(ports[i].name, expected_names[i]) << "port " << i;
    EXPECT_EQ(ports[i].data_type.kind, DataTypeKind::kLogic) << "port " << i;
  }
}
TEST(ParserSection23, AnsiPortsWithDefaultType) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
}

TEST(ParserSection6, Sec6_11_IntegerTypesAsPortDecls) {
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

TEST(ParserSection6, Sec6_11_LongintShortintAsPorts) {
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

TEST(ParserSection6, Sec6_11_LogicPackedDimsAsPort) {
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

TEST(ParserSection6, Sec6_11_IntegerAsPort) {
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

TEST(ParserSection6, VarImplicitInPort) {
  EXPECT_TRUE(
      ParseOk("module t(input var [7:0] data_in);\n"
              "endmodule\n"));
}

TEST(ParserSection6, ShortrealInPort) {
  EXPECT_TRUE(
      ParseOk("module m (input var shortreal in_val,\n"
              "          output var shortreal out_val);\n"
              "  assign out_val = in_val;\n"
              "endmodule\n"));
}

}
