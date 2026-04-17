#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ModportExpressionParsing, ModportSimplePortExplicitExpr) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  modport mp(input .x(a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "x");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, PartSelectPortExpression) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] r;\n"
      "  modport A(output .P(r[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, PortExprEmpty) {
  auto r = Parse(
      "interface bus;\n"
      "  modport A(input .P());\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, PortExpressionMixedWithBareIdentifier) {
  auto r = Parse(
      "interface I;\n"
      "  logic [7:0] r;\n"
      "  bit R;\n"
      "  modport A(output .P(r[3:0]), R);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
  EXPECT_EQ(mp->ports[1].name, "R");
}

TEST(ModportExpressionParsing, DotNotationPortNameAndExpr) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, ModportPortExpressionPartSelect) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, DotNotationAfterDirectionPort) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  logic clk;\n"
      "  modport target(input clk, .data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[1].name, "data");
  EXPECT_NE(mp->ports[1].expr, nullptr);
}

TEST(ModportExpressionParsing, DotNotationWithoutDirection) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  modport mp(.x(a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "x");
  EXPECT_NE(mp->ports[0].expr, nullptr);
  EXPECT_EQ(mp->ports[0].direction, Direction::kNone);
}

TEST(ModportExpressionParsing, BitSelectPortExpression) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] r;\n"
      "  modport A(input .P(r[3]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, ConcatenationPortExpression) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b;\n"
      "  modport A(input .P({a, b}));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, ConstantPortExpression) {
  auto r = Parse(
      "interface bus;\n"
      "  modport A(input .P(2));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

}  // namespace
