#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(NonAnsiStylePortDeclarations, BasicInputOutput) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(NonAnsiStylePortDeclarations, InputWithPackedDims) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(NonAnsiStylePortDeclarations, OutputRegType) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(NonAnsiStylePortDeclarations, MixedDirections) {
  auto r = Parse(
      "module m(a, b, c, d);\n"
      "  input a, b;\n"
      "  output [3:0] c;\n"
      "  inout d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  struct Expected {
    const char* name;
    Direction dir;
  };
  Expected expected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kInput},
      {"c", Direction::kOutput},
      {"d", Direction::kInout},
  };
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
  EXPECT_NE(mod->ports[2].data_type.packed_dim_left, nullptr);
}

TEST(NonAnsiStylePortDeclarations, MultipleDeclarations) {
  auto r = Parse(
      "module m (a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  EXPECT_TRUE(
      ParseOk("module m (a, d); input [15:0] a; inout [7:0] d; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m (a, b); inout [7:0] a; inout [7:0] b; endmodule\n"));
}

TEST(NonAnsiStylePortDeclarations, InoutPort) {
  auto r = Parse(
      "module m(bus);\n"
      "  inout [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(NonAnsiStylePortDeclarations, MultiplePortsSameDirection) {
  auto r = Parse(
      "module m(x, y, z);\n"
      "  output x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(mod->ports[i].direction, Direction::kOutput);
  }
}

TEST(NonAnsiStylePortDeclarations, ImplicitPortDirectionNone) {
  auto r = Parse("module m(a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kNone);
}

TEST(NonAnsiStylePortDeclarations, RefPort) {
  auto r = Parse(
      "module m(d);\n"
      "  ref logic [7:0] d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
}

TEST(NonAnsiStylePortDeclarations, PortListMultipleNames) {
  auto r = Parse("module m(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "c");
}

TEST(NonAnsiStylePortDeclarations, ExplicitPortWithExpression) {
  auto r = Parse("module m(.a(x), .b(y)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "a");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(mod->ports[1].name, "b");
  ASSERT_NE(mod->ports[1].port_expr, nullptr);
}

TEST(NonAnsiStylePortDeclarations, ExplicitPortEmptyExpression) {
  auto r = Parse("module m(.a(), .b(y)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[1].name, "b");
  ASSERT_NE(mod->ports[1].port_expr, nullptr);
}

TEST(NonAnsiStylePortDeclarations, ConcatenationPortExpression) {
  auto r = Parse("module m({c, d}); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_TRUE(mod->ports[0].name.empty());
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kConcatenation);
}

TEST(NonAnsiStylePortDeclarations, BitSelectInPortList) {
  auto r = Parse("module m(a[3]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "a");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kSelect);
}

TEST(NonAnsiStylePortDeclarations, PartSelectInPortList) {
  auto r = Parse("module m(a[7:4], a[3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(mod->ports[i].name, "a");
    ASSERT_NE(mod->ports[i].port_expr, nullptr);
    EXPECT_EQ(mod->ports[i].port_expr->kind, ExprKind::kSelect);
  }
}

TEST(NonAnsiStylePortDeclarations, ExplicitPortWithConcatenation) {
  auto r = Parse("module m(.a({b, c})); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "a");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kConcatenation);
}

TEST(NonAnsiStylePortDeclarations, MixedImplicitAndExplicitPorts) {
  auto r = Parse("module m({c, d}, .e(f)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_TRUE(mod->ports[0].name.empty());
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(mod->ports[1].name, "e");
  ASSERT_NE(mod->ports[1].port_expr, nullptr);
}

TEST(NonAnsiStylePortDeclarations, TwoExplicitPortsSameNet) {
  auto r = Parse("module m(.a(i), .b(i)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[1].name, "b");
}

TEST(NonAnsiStylePortDeclarations, ExplicitPortConcatSelectAndImplicit) {
  auto r = Parse("module m(.a({b, c}), f, .g(h[1])); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].name, "a");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(mod->ports[1].name, "f");
  EXPECT_EQ(mod->ports[1].port_expr, nullptr);
  EXPECT_EQ(mod->ports[2].name, "g");
  ASSERT_NE(mod->ports[2].port_expr, nullptr);
  EXPECT_EQ(mod->ports[2].port_expr->kind, ExprKind::kSelect);
}

TEST(NonAnsiStylePortDeclarations, TwoImplicitPortsSameName) {
  auto r = Parse(
      "module m(a, a);\n"
      "  input a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "a");
}

TEST(NonAnsiStylePortDeclarations, MixedDirectionExplicitPort) {
  auto r = Parse(
      "module m(.p({a, e}));\n"
      "  input a;\n"
      "  output e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].name, "p");
  ASSERT_NE(mod->ports[0].port_expr, nullptr);
  EXPECT_EQ(mod->ports[0].port_expr->kind, ExprKind::kConcatenation);
}

TEST(NonAnsiStylePortDeclarations, EmptyPortSlot) {
  EXPECT_TRUE(ParseOk("module m(a, , b); endmodule\n"));
}

TEST(NonAnsiStylePortDeclarations, InputSignedAttribute) {
  auto r = Parse(
      "module m(a);\n"
      "  input signed [7:0] a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].data_type.is_signed);
}

TEST(NonAnsiStylePortDeclarations, PortDeclWithNetType) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input wire [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(NonAnsiStylePortDeclarations, Example1SignednessParses) {
  EXPECT_TRUE(ParseOk(
      "module test(a, b, c, d, e, f, g, h);\n"
      "  input [7:0] a;\n"
      "  input [7:0] b;\n"
      "  input signed [7:0] c;\n"
      "  input signed [7:0] d;\n"
      "  output [7:0] e;\n"
      "  output [7:0] f;\n"
      "  output signed [7:0] g;\n"
      "  output signed [7:0] h;\n"
      "  wire signed [7:0] b;\n"
      "  wire [7:0] c;\n"
      "  logic signed [7:0] f;\n"
      "  logic [7:0] g;\n"
      "endmodule\n"));
}

}  // namespace
