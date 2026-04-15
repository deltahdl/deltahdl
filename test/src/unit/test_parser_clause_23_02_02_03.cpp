

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- ANSI/non-ANSI detection (D1) ---

TEST(PortDeclParsing, FirstPortAllOmittedIsNonAnsi) {
  auto r = Parse(
      "module m(x, y);\n"
      "  input x;\n"
      "  output y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->is_non_ansi_ports);
}

TEST(PortDeclParsing, FirstPortWithTypeKeywordIsAnsi) {
  auto r = Parse("module m(wire x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->is_non_ansi_ports);
}

// --- First port: direction omitted defaults to inout ---

TEST(PortDeclParsing, OmittedDirectionWithWireDefaultsToInout) {
  auto r = Parse("module m(wire x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(port.data_type.is_net);
  EXPECT_EQ(port.name, "x");
}

TEST(PortDeclParsing, OmittedDirectionWithIntegerDefaultsToInout) {
  auto r = Parse("module m(integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
}

TEST(PortDeclParsing, OmittedDirectionWithPackedDimsDefaultsToInout) {
  auto r = Parse("module m([5:0] x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(PortDeclParsing, OmittedDirectionWithVarDefaultsToInout) {
  auto r = Parse("module m(var x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
}

// --- First port: data type omitted defaults to logic ---

TEST(PortDeclParsing, InputOmittedTypeDefaultsToLogic) {
  auto r = Parse("module m(input x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
}

TEST(PortDeclParsing, OutputOmittedTypeDefaultsToLogic) {
  auto r = Parse("module m(output x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
}

TEST(PortDeclParsing, InoutOmittedTypeDefaultsToLogic) {
  auto r = Parse("module m(inout x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
}

TEST(PortDeclParsing, RefOmittedTypeDefaultsToLogic) {
  auto r = Parse("module m(ref x [5:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
}

// --- First port: port kind defaults for input/inout (net) ---

TEST(PortDeclParsing, InputKindOmittedDefaultsToNet) {
  auto r = Parse("module m(input x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_net);
}

TEST(PortDeclParsing, InoutKindOmittedDefaultsToNet) {
  auto r = Parse("module m(inout x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_net);
}

TEST(PortDeclParsing, InoutExplicitIntegerKindDefaultsToNet) {
  auto r = Parse("module m(inout integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(port.data_type.is_net);
}

// --- First port: output kind defaults (implicit→net, explicit→variable) ---

TEST(PortDeclParsing, OutputImplicitTypeKindDefaultsToNet) {
  auto r = Parse("module m(output x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_net);
}

TEST(PortDeclParsing, OutputSignedImplicitTypeKindDefaultsToNet) {
  auto r = Parse("module m(output signed [5:0] x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(port.data_type.is_net);
  EXPECT_TRUE(port.data_type.is_signed);
}

TEST(PortDeclParsing, OutputExplicitIntegerKindDefaultsToVar) {
  auto r = Parse("module m(output integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, OutputExplicitLogicKindDefaultsToVar) {
  auto r = Parse("module m(output logic x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(port.data_type.is_net);
}

// --- First port: ref is always variable ---

TEST(PortDeclParsing, RefKindIsAlwaysVariable) {
  auto r = Parse("module m(ref [5:0] x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.data_type.is_net);
}

// --- First port: input var / output var ---

TEST(PortDeclParsing, InputVarOmittedTypeDefaultsToVarLogic) {
  auto r = Parse("module m(input var x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, OutputVarOmittedTypeDefaultsToVarLogic) {
  auto r = Parse("module m(output var x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, InputVarIntegerIsVariable) {
  auto r = Parse("module m(input var integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
  EXPECT_FALSE(port.data_type.is_net);
}

// --- Subsequent port: all omitted inherits all from previous ---

TEST(PortDeclParsing, AllOmittedSubsequentInheritsAll) {
  auto r = Parse("module m(wire x, y[7:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInout);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(ports[0].data_type.is_net);
  EXPECT_EQ(ports[1].direction, Direction::kInout);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(ports[1].data_type.is_net);
  EXPECT_EQ(ports[1].name, "y");
  EXPECT_FALSE(ports[1].unpacked_dims.empty());
}

TEST(PortDeclParsing, AllOmittedSubsequentInheritsRef) {
  auto r = Parse("module m(ref [5:0] x, y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[1].direction, Direction::kRef);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(ports[1].data_type.is_net);
  EXPECT_NE(ports[1].data_type.packed_dim_left, nullptr);
}

// --- Subsequent port: unpacked dims not inherited ---

TEST(PortDeclParsing, UnpackedDimsNotInheritedFromPrevious) {
  auto r = Parse("module m(ref x [5:0], y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_FALSE(ports[0].unpacked_dims.empty());
  EXPECT_TRUE(ports[1].unpacked_dims.empty());
  EXPECT_EQ(ports[1].direction, Direction::kRef);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
}

// --- Subsequent port: direction omitted inherits from previous ---

TEST(PortDeclParsing, OmittedDirectionOnSubsequentInherits) {
  auto r = Parse("module m(input var integer x, wire y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(ports[1].data_type.is_net);
}

// --- Subsequent port: new direction resets kind and type ---

TEST(PortDeclParsing, NewDirectionResetsKindAndType) {
  auto r = Parse("module m(output var x, input y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kOutput);
  EXPECT_FALSE(ports[0].data_type.is_net);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(ports[1].data_type.is_net);
}

// --- Subsequent port: explicit type uses first-port kind rules ---

TEST(PortDeclParsing, ExplicitTypeOnSubsequentUsesOutputVarRule) {
  auto r = Parse("module m(output signed [5:0] x, integer y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kOutput);
  EXPECT_TRUE(ports[0].data_type.is_net);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kInteger);
  EXPECT_FALSE(ports[1].data_type.is_net);
}

// --- Subsequent port: type change resets to logic ---

TEST(PortDeclParsing, TypeChangeOnSubsequentResetsToLogic) {
  auto r = Parse("module m(integer x, signed [5:0] y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(ports[1].direction, Direction::kInout);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(ports[1].data_type.is_signed);
  EXPECT_TRUE(ports[1].data_type.is_net);
}

// --- Explicit port: inherits only direction, not kind or type ---

TEST(PortDeclParsing, ExplicitPortInheritsOnlyDirection) {
  auto r = Parse(
      "module m(input integer p_a, .p_b(s_b), p_c);\n"
      "  logic [5:0] s_b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(ports[0].name, "p_a");
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[1].name, "p_b");
  EXPECT_NE(ports[1].port_expr, nullptr);
  EXPECT_EQ(ports[2].direction, Direction::kInput);
  EXPECT_EQ(ports[2].data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(ports[2].data_type.is_net);
  EXPECT_EQ(ports[2].name, "p_c");
}

}  // namespace
