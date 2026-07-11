#include <string_view>

#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

ModuleItem* FirstItemOfKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// §16.12.7: the overlapped implication form `sequence_expr |-> property_expr`
// is accepted at the property level of a concurrent assertion.
TEST(AssertionSemanticsParsing, OverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.12.7: the nonoverlapped implication form `sequence_expr |=>
// property_expr` is likewise accepted at the property level of a concurrent
// assertion.
TEST(AssertionSemanticsParsing, NonoverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.12.7 input form — antecedent operand type: the antecedent of an
// implication is a sequence_expr, which may be a genuine multi-tick sequence
// rather than a single sampled boolean. Built here from real §16.7 sequence
// delay (`##`) syntax with a sequence consequent, the overlapped implication is
// accepted at the property level of a concurrent assertion.
TEST(AssertionSemanticsParsing, SequenceAntecedentOverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) (a ##1 b ##1 c) |-> (d ##1 e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.12.7 input form — syntactic position: the nonoverlapped implication is
// accepted at the property level of an `assume property` directive, a distinct
// property-level position from `assert property`.
TEST(AssertionSemanticsParsing, NonoverlapImplicationInAssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssumeProperty));
}

// §16.12.7 input form — syntactic position: an implication is also accepted at
// the property level of a `cover property` directive.
TEST(AssertionSemanticsParsing, OverlapImplicationInCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) start |-> busy);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kCoverProperty));
}

// §16.12.7 input form — syntactic position: an implication forms the body
// property_spec of a named property declaration, another property-level
// position. The nonoverlapped operator here is built over a real §16.9.2.1
// clocking event.
TEST(AssertionSemanticsParsing, ImplicationInNamedPropertyDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

// §16.12.7 input form — operand nesting: the consequent of an implication is
// itself a property_expr, so implications nest (the nested-implication form the
// LRM discusses). Here the right operand `b |=> c` is a further implication,
// which the property level accepts.
TEST(AssertionSemanticsParsing, NestedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b |=> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.12.7: the parser recognizes |-> and |=> as temporal property operators.
// Production (BodyHasTemporalOperator) classifies a clocked property body
// containing either operator as a full property spec — skipped to the
// "<property_spec>" placeholder — rather than as a simple sampled boolean, so
// seeing that placeholder confirms the operator was recognized. A clocked body
// with no implication operator takes the simple-boolean path instead, keeping a
// real parsed expression; contrasting the two shows the classification is
// driven by the presence of the implication operator.
TEST(AssertionSemanticsParsing,
     ImplicationOperatorDrivesTemporalClassification) {
  const std::string_view placeholder = "<property_spec>";

  auto overlap = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(overlap.cu, nullptr);
  auto* ov = FirstItemOfKind(overlap, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ov, nullptr);
  ASSERT_NE(ov->assert_expr, nullptr);
  EXPECT_EQ(ov->assert_expr->text, placeholder);

  auto nonoverlap = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |=> b);\n"
      "endmodule\n");
  ASSERT_NE(nonoverlap.cu, nullptr);
  auto* no = FirstItemOfKind(nonoverlap, ModuleItemKind::kAssertProperty);
  ASSERT_NE(no, nullptr);
  ASSERT_NE(no->assert_expr, nullptr);
  EXPECT_EQ(no->assert_expr->text, placeholder);

  // Contrast: a clocked property with no implication operator is a simple
  // sampled boolean, so it is not reduced to the property-spec placeholder.
  auto boolean = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b);\n"
      "endmodule\n");
  ASSERT_NE(boolean.cu, nullptr);
  auto* bl = FirstItemOfKind(boolean, ModuleItemKind::kAssertProperty);
  ASSERT_NE(bl, nullptr);
  ASSERT_NE(bl->assert_expr, nullptr);
  EXPECT_NE(bl->assert_expr->text, placeholder);
}

}  // namespace
