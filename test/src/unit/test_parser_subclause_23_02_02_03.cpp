

#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(PortDeclParsing, OmittedDirectionWithPackedDimsDefaultsToInout) {
  auto r = Parse("module m([5:0] x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

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

TEST(PortDeclParsing, FirstPortExplicitTypeOmittedDirectionDefaultsToInout) {
  // §23.2.2.3: an explicit data type makes the first port ANSI-style even with
  // no direction keyword, so the omitted direction defaults to inout. With the
  // port kind also omitted, an inout port becomes a net.
  auto r = Parse("module m(integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->is_non_ansi_ports);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(port.data_type.is_net);
}

TEST(PortDeclParsing, InputExplicitIntegerKindDefaultsToNet) {
  // §23.2.2.3: an input port with the port kind omitted defaults to a net, even
  // when the data type is given explicitly rather than left implicit.
  auto r = Parse("module m(input integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(port.data_type.is_net);
}

TEST(PortDeclParsing, RefExplicitTypeIsAlwaysVariable) {
  // §23.2.2.3: a ref port is always a variable; this holds even when the data
  // type is stated explicitly, so the ref rule overrides the net defaults that
  // an explicit type would otherwise leave in place for other directions.
  auto r = Parse("module m(ref integer x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kInteger);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, InputKindOmittedDefaultsToNet) {
  auto r = Parse("module m(input x); endmodule");
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

TEST(PortDeclParsing, OutputExplicitLogicKindDefaultsToVar) {
  auto r = Parse("module m(output logic x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, RefKindIsAlwaysVariable) {
  auto r = Parse("module m(ref [5:0] x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, InputVarOmittedTypeDefaultsToVarLogic) {
  auto r = Parse("module m(input var x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
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

TEST(PortDeclParsing, VarOnlyFirstPortDefaultsToInoutVariable) {
  // §23.2.2.3 (LRM example mh4): the port kind is given (var) but the direction
  // is omitted, so for the first port the direction defaults to inout while the
  // explicit var keeps the port a variable rather than a net. This is exactly
  // the state the LRM flags as an error, because an inout port may not be a
  // variable; the parser resolves the defaults here, the elaborator rejects the
  // combination (see the matching elaborator test).
  auto r = Parse("module m(var x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->is_non_ansi_ports);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(port.data_type.is_net);
}

TEST(PortDeclParsing, InterconnectPortGetsNoLogicDataType) {
  // §23.2.2.3: the rule that an omitted data type defaults to logic is
  // explicitly excepted for interconnect ports, which carry no data type.
  // The resolved port therefore stays interconnect rather than logic.
  auto r = Parse("module m(interconnect x); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_TRUE(port.data_type.is_interconnect);
  EXPECT_NE(port.data_type.kind, DataTypeKind::kLogic);
}

TEST(PortDeclParsing, SubsequentPortInheritsInterconnect) {
  // §23.2.2.3: when a subsequent port omits direction, port kind, and data
  // type, those are inherited from the previous port; if the previous port
  // was an interconnect port, this port is interconnect as well.
  auto r = Parse("module m(interconnect x, y); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_TRUE(ports[0].data_type.is_interconnect);
  EXPECT_EQ(ports[1].direction, Direction::kInout);
  EXPECT_TRUE(ports[1].data_type.is_interconnect);
  EXPECT_EQ(ports[1].name, "y");
}

}  // namespace
