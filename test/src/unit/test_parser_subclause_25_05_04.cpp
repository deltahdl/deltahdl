#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

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

TEST(ModportExpressionParsing, DotNotationWithoutDirection) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  modport mp(.x(a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "a modport_ports_declaration opens with a port_direction", 3,
      "A.2.9"));
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "x");
  EXPECT_NE(mp->ports[0].expr, nullptr);
  EXPECT_EQ(mp->ports[0].direction, Direction::kNone);
}

TEST(ModportExpressionParsing, ConcatenationExpressionCaptured) {
  auto r = Parse(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(output .P({a, b}));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportExpressionParsing, AssignmentPatternExpressionCaptured) {
  auto r = Parse(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(input .P('{a, b}));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

}  // namespace
