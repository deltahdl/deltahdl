#include "fixture_parser.h"

using namespace delta;

namespace {

// N6: the bound expression is optional — `.P()` declares a port that connects
// to nothing internal, leaving the expression null.
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

// N1: a `.port_id(expression)` modport expression parses with its bound
// expression captured, and the modport-item loop continues past it to a plain
// bare-identifier port in the same list. The LRM's own `.P(r[3:0])` part-select
// stands in for every expression kind ParseExpr accepts (array/struct element,
// bit-select, concatenation, assignment pattern, constant) — all share this one
// parse branch, so a single representative observes it.
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

// N1: a modport expression with no preceding direction keyword parses with
// direction kNone (the default-direction path of the modport-item loop).
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

// N1 (concatenation input form): a modport expression whose bound expression is
// a concatenation of interface elements parses with the concatenation captured.
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

// N1 (assignment-pattern input form): a modport expression whose bound
// expression is an assignment pattern parses with the expression captured.
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
