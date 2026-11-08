#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

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
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[1].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].width, 6u);
}

TEST(PortKindDataTypeDirection, ExplicitPortOverTwoStateObjectsIsBit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .p({x, y}), output .q({x, z}));\n"
      "  bit x; bit [1:0] y; logic z;\n"
      "endmodule",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].type_kind, DataTypeKind::kBit);
  EXPECT_EQ(ports[0].width, 3u);
  EXPECT_EQ(ports[1].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].width, 2u);
}

TEST(PortKindDataTypeDirection, VarFirstPortDefaultedToInoutIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m(var x); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable data type is not permitted on inout port "
                            "'x'",
                            1, "23.3.3.2"));
}

TEST(PortKindDataTypeDirection, FirstPortExplicitTypeElaboratesAsInoutNet) {
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
  ElabFixture f;
  auto* design = ElaborateSrc("module m(input x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->ports[0].is_var);
}

TEST(PortKindDataTypeDirection, OutputImplicitTypeElaboratesAsNet) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(output [5:0] x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_FALSE(port.is_var);
}

TEST(PortKindDataTypeDirection, OutputExplicitTypeElaboratesAsVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(output logic x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_TRUE(port.is_var);
}

TEST(PortKindDataTypeDirection, RefPortElaboratesAsVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(ref [5:0] x); endmodule", f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_TRUE(port.is_var);
}

TEST(PortKindDataTypeDirection, RefPortDeclaredWithANetTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m(ref wire logic x, ref logic y);\n"
      "endmodule\n"
      "module n(z);\n"
      "  ref tri logic z;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c;\n"
      "  m u1(a, b);\n"
      "  n u2(c);\n"
      "endmodule\n",
      f, "top");
  const char* message = "is declared with a net type; a ref port is a variable";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 1, "23.2.2.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "23.2.2.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "ref port 'y'", 1, "23.2.2.3"));
}

TEST(PortKindDataTypeDirection, ANetPortOfATypeNoNetCanHaveIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input string s,\n"
      "         input real r,\n"
      "         inout event e,\n"
      "         input var string v);\n"
      "endmodule\n",
      f, "m");
  for (uint32_t line : {1u, 2u, 3u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "net data type must be 4-state", line, "6.7.1"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "net data type must be 4-state", 4, "6.7.1"));
}

}  // namespace
