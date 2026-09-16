#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.12.18: a `property`-typed formal may appear in the consequent of an
// implication, because the consequent is a property_expr position. Placing the
// formal as the consequent of `|->` is therefore legal.
TEST(TypedPropertyFormalParsing, PropertyTypedFormalAsConsequentParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    b |-> q;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18: a `property`-typed formal may not be referenced as the antecedent
// of an overlapping implication `|->` (see §16.12.7), regardless of the actual
// argument, because a property_expr may not be written in that position. The
// body scan rejects the reference standing in the antecedent position.
TEST(TypedPropertyFormalParsing,
     PropertyTypedFormalAsOverlapAntecedentRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    q |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a 'property'-typed formal argument may not be "
                            "referenced as the antecedent of '|->' or '|=>'",
                            3, "16.12.18"));
}

// §16.12.18: the same prohibition covers the non-overlapping implication `|=>`,
// whose antecedent is likewise a sequence_expr position where a property_expr
// may not be written.
TEST(TypedPropertyFormalParsing,
     PropertyTypedFormalAsNonOverlapAntecedentRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    q |=> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a 'property'-typed formal argument may not be "
                            "referenced as the antecedent of '|->' or '|=>'",
                            3, "16.12.18"));
}

// §16.12.18: the prohibition is specific to `property`-typed formals. A
// `sequence`-typed formal is a legal antecedent of an implication (a sequence
// may be written in the antecedent position), so the same shape with a sequence
// formal parses cleanly. This confirms the rule keys off the formal's declared
// type, not merely the syntactic position.
TEST(TypedPropertyFormalParsing, SequenceTypedFormalAsAntecedentParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(sequence q);\n"
      "    q |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18: the `property` type keyword qualifies the whole comma-separated
// run of formal names until a differently typed item begins, so in `property q,
// r` both q and r are property-typed. A reference to the second name r as an
// implication antecedent is therefore rejected just as the first would be,
// confirming the carry-over of the property_formal_type across the port run.
TEST(TypedPropertyFormalParsing, PropertyTypeCarriesOverCommaSeparatedRun) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q, r);\n"
      "    r |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a 'property'-typed formal argument may not be "
                            "referenced as the antecedent of '|->' or '|=>'",
                            3, "16.12.18"));
}

// §16.12.18: the property run is ended not only by a §16.6 data type but by any
// non-property formal type keyword — `sequence`, `event`, or `untyped`. Here an
// active property run started by `property a` is cleared by the `event`
// keyword, so the second formal b is event-typed, not property-typed, and may
// legally head an implication. This exercises the run-clearing path distinct
// from the data-type case (a different type-keyword handler) and confirms the
// rule keys strictly off the `property` type.
TEST(TypedPropertyFormalParsing, EventTypeKeywordEndsActivePropertyRun) {
  auto r = Parse(
      "module m;\n"
      "  property p(property a, event b);\n"
      "    b |-> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18: a data-type (§16.6) formal item ends the property run, so a formal
// declared after a `property` name but with an intervening data type is not
// property-typed and may legally head an implication. Here q is property-typed
// but r is `bit`-typed; referencing r as an antecedent raises no diagnostic,
// showing the run ends at the fresh type specifier.
TEST(TypedPropertyFormalParsing, DataTypeFormalEndsPropertyRun) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q, bit r);\n"
      "    r |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
}

// §16.12.18 by way of §16.8.1: the type a formal is declared with is
// recorded by its keyword for every formal the keyword reaches, `property`,
// `sequence` and `event` as themselves, so that an instance's actuals are
// cast and read as the types say.
TEST(TypedPropertyFormalParsing, TheTypeKeywordOfEachFormalIsRecorded) {
  auto r = Parse(
      "module m;\n"
      "  property p(bit x, y, event e, sequence s, property q, untyped u);\n"
      "    @(e) x |-> y;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formal_type_kw.size(), 6u);
  EXPECT_EQ(item->prop_formal_type_kw[0], TokenKind::kKwBit);
  EXPECT_EQ(item->prop_formal_type_kw[1], TokenKind::kKwBit);
  EXPECT_EQ(item->prop_formal_type_kw[2], TokenKind::kKwEvent);
  EXPECT_EQ(item->prop_formal_type_kw[3], TokenKind::kKwSequence);
  EXPECT_EQ(item->prop_formal_type_kw[4], TokenKind::kKwProperty);
  EXPECT_EQ(item->prop_formal_type_kw[5], TokenKind::kEof);
}

// §16.12.18: the actual for a formal of type property may be a
// sequence_expr, which no expression holds, so the instance standing as
// the whole property_spec is read with the actual as a sequence, carried
// by the argument for the substitution to read.
TEST(TypedPropertyFormalParsing, ASequenceActualIsReadAsASequence) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    @(posedge clk) a |-> q;\n"
      "  endproperty\n"
      "  assert property (p(b ##1 c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_expr, nullptr);
  EXPECT_EQ(item->assert_expr->kind, ExprKind::kCall);
  ASSERT_EQ(item->assert_expr->args.size(), 1u);
  const PropertyExprNode* actual = item->assert_expr->args[0]->property_actual;
  ASSERT_NE(actual, nullptr);
  EXPECT_EQ(actual->kind, PropertyExprNode::Kind::kSequence);
  ASSERT_NE(actual->sequence, nullptr);
  EXPECT_EQ(actual->sequence->seq_linear.operands.size(), 2u);
}

// §16.12.18: the actual may be a property_expr of any form, read as the
// tree an assertion's property is, here under the assertion's own clock; a
// second actual that is an expression is read as one.
TEST(TypedPropertyFormalParsing, APropertyActualIsReadAsATree) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q, r);\n"
      "    @(posedge clk) a |-> q;\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) p(b |-> nexttime c, d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_expr, nullptr);
  EXPECT_EQ(item->assert_expr->kind, ExprKind::kCall);
  ASSERT_EQ(item->assert_expr->args.size(), 2u);
  const PropertyExprNode* actual = item->assert_expr->args[0]->property_actual;
  ASSERT_NE(actual, nullptr);
  EXPECT_EQ(actual->kind, PropertyExprNode::Kind::kImplication);
  ASSERT_EQ(actual->operands.size(), 1u);
  EXPECT_EQ(actual->operands[0]->kind, PropertyExprNode::Kind::kNexttime);
  EXPECT_EQ(item->assert_expr->args[1]->property_actual, nullptr);
  EXPECT_EQ(item->assert_expr->args[1]->text, "d");
}

// §16.12.18 by way of §16.8.1: the actual for a formal of type event is an
// event expression, read as the edge over its signal.
TEST(TypedPropertyFormalParsing, AnEventActualIsReadAsTheEdgeOverItsSignal) {
  auto r = Parse(
      "module m;\n"
      "  property p(event ev);\n"
      "    @(ev) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p(negedge clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_expr, nullptr);
  ASSERT_EQ(item->assert_expr->args.size(), 1u);
  const Expr* actual = item->assert_expr->args[0];
  EXPECT_EQ(actual->kind, ExprKind::kUnary);
  EXPECT_EQ(actual->op, TokenKind::kKwNegedge);
  ASSERT_NE(actual->lhs, nullptr);
  EXPECT_EQ(actual->lhs->text, "clk");
}

}  // namespace
