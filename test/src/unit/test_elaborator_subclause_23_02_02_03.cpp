
#include "fixture_elaborator.h"

namespace {

TEST(PortKindDataTypeDirection, OmittedDirectionElaboratesToInout) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(wire x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(design->top_modules[0]->ports[0].width, 1u);
}

TEST(PortKindDataTypeDirection, OmittedTypeElaboratesAsLogicWidth1) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(input x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 1u);
}

TEST(PortKindDataTypeDirection, InheritedPortElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic [7:0] x, y);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  auto& py = design->top_modules[0]->ports[1];
  EXPECT_EQ(py.direction, Direction::kInput);
  EXPECT_EQ(py.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(py.width, 8u);
}

TEST(PortKindDataTypeDirection, OutputExplicitIntegerElaboratesWidth32) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output integer x);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kInteger);
  EXPECT_EQ(port.width, 32u);
}

TEST(PortKindDataTypeDirection, SignedImplicitTypeElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output signed [5:0] x);\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 6u);
  EXPECT_TRUE(port.is_signed);
}

TEST(PortKindDataTypeDirection, ExplicitPortTakesExpressionDataType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input integer p_a, .p_b(s_b), p_c);\n"
      "  logic [5:0] s_b;\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  // §23.2.2.3: the explicitly named port p_b takes the self-determined data
  // type of its connection expression s_b, a 6-bit value declared in the body.
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[1].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].width, 6u);
}

TEST(PortKindDataTypeDirection, VarFirstPortDefaultedToInoutIsRejected) {
  // §23.2.2.3 (LRM example mh4): a first port declared only with var omits the
  // direction, which defaults to inout. An inout port may not carry a variable
  // data type, so applying the default-direction rule surfaces the error the
  // LRM documents for mh4. The rejection is observable only after elaboration.
  ElabFixture f;
  ElaborateSrc("module m(var x); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(PortKindDataTypeDirection, FirstPortExplicitTypeElaboratesAsInoutNet) {
  // §23.2.2.3: an explicit data type on the first port with no direction
  // keyword still resolves to an inout port (direction default) that is a net
  // (inout port kind default), carrying the explicit type's width through
  // elaboration.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(integer x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.type_kind, DataTypeKind::kInteger);
  EXPECT_FALSE(port.is_var);
  EXPECT_EQ(port.width, 32u);
}

TEST(PortKindDataTypeDirection, InputOmittedKindElaboratesAsNet) {
  // §23.2.2.3: for an input port with the port kind omitted, the kind defaults
  // to a net; the elaborated port therefore is not a variable.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(input x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->ports[0].is_var);
}

TEST(PortKindDataTypeDirection, OutputImplicitTypeElaboratesAsNet) {
  // §23.2.2.3: an output port whose data type is left implicit (only a packed
  // range here) defaults its port kind to a net, so is_var is false.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(output [5:0] x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_FALSE(port.is_var);
}

TEST(PortKindDataTypeDirection, OutputExplicitTypeElaboratesAsVariable) {
  // §23.2.2.3: an output port declared with an explicit data type defaults its
  // port kind to variable, so the elaborated port reports is_var.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(output logic x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_TRUE(port.is_var);
}

TEST(PortKindDataTypeDirection, RefPortElaboratesAsVariable) {
  // §23.2.2.3: a ref port is always a variable, independent of its data type.
  ElabFixture f;
  auto* design = ElaborateSrc("module m(ref [5:0] x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_TRUE(port.is_var);
}

}  // namespace
