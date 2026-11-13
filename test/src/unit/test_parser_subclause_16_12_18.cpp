#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(item->prop_formal_type_kw[5], TokenKind::kKwUntyped);
}

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
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* root = item->body->assert_property;
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->kind, PropertyExprNode::Kind::kBoolean);
  const Expr* instance = root->boolean;
  ASSERT_NE(instance, nullptr);
  EXPECT_EQ(instance->kind, ExprKind::kCall);
  ASSERT_EQ(instance->args.size(), 2u);
  const PropertyExprNode* actual = instance->args[0]->property_actual;
  ASSERT_NE(actual, nullptr);
  EXPECT_EQ(actual->kind, PropertyExprNode::Kind::kImplication);
  ASSERT_EQ(actual->operands.size(), 1u);
  EXPECT_EQ(actual->operands[0]->kind, PropertyExprNode::Kind::kNexttime);
  EXPECT_EQ(instance->args[1]->property_actual, nullptr);
  EXPECT_EQ(instance->args[1]->text, "d");
}

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

TEST(TypedPropertyFormalParsing, AClockedBooleanBodyIsCapturedAsATreeToo) {
  auto r = Parse(
      "module m;\n"
      "  property p(property q);\n"
      "    @(posedge clk) not q;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->prop_body_expr, nullptr);
  EXPECT_TRUE(item->prop_negated);
  ASSERT_NE(item->prop_body_tree, nullptr);
  EXPECT_EQ(item->prop_body_tree->kind, PropertyExprNode::Kind::kNot);
  ASSERT_EQ(item->prop_body_tree->operands.size(), 1u);
  const PropertyExprNode* operand = item->prop_body_tree->operands[0];
  EXPECT_EQ(operand->kind, PropertyExprNode::Kind::kBoolean);
  ASSERT_NE(operand->boolean, nullptr);
  EXPECT_EQ(operand->boolean->text, "q");
}

TEST(TypedPropertyFormalParsing, AUserDefinedTypeEndsAPropertyRun) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [1:0] my_t;\n"
      "  property p(property q, my_t x);\n"
      "    q;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formal_is_property.size(), 2u);
  EXPECT_TRUE(item->prop_formal_is_property[0]);
  EXPECT_FALSE(item->prop_formal_is_property[1]);
}

constexpr const char* kPropertyFormalPlaces[] = {
    "module",  "interface", "program",  "checker",
    "package", "generate",  "clocking", "unit"};

std::string PropertyFormalIn(const std::string& place,
                             const std::string& body) {
  const std::string kSignals =
      "  bit clk, a, b; sequence s(z); z; endsequence sequence st(sequence "
      "z); z; endsequence property r(property z); z; endproperty\n";
  const std::string kDeclared =
      "property p(property q); " + body + "; endproperty";
  if (place == "unit") return "\n" + kSignals + "  " + kDeclared + "\n";
  std::string line = "  " + kDeclared;
  if (place == "generate") line = "  if (1) begin : g " + kDeclared + " end";
  if (place == "clocking") {
    line = "  clocking cb @(posedge clk); " + kDeclared + " endclocking";
  }
  std::string unit =
      place == "generate" || place == "clocking" ? "module" : place;
  return unit + " m;\n" + kSignals + line + "\nend" + unit + "\n";
}

constexpr const char* kPropertyFormalReference =
    "a 'property'-typed formal argument may not be referenced";

void ExpectPropertyFormalReported(const char* place, const char* body) {
  SCOPED_TRACE(std::string(place) + " " + body);
  auto r = Parse(PropertyFormalIn(place, body));
  EXPECT_TRUE(ReportedError(r.diags, kPropertyFormalReference, 3, "16.12.18"));
}

TEST(TypedPropertyFormalParsing,
     AnImplicationAntecedentIsReportedInEachPlaceAndNesting) {
  for (const char* place : kPropertyFormalPlaces) {
    for (const char* body :
         {"q |-> b", "q |=> b", "b |-> (q |=> b)", "not (q |-> b)",
          "if (a) (q |-> b)", "if (a) b else (q |=> b)"}) {
      ExpectPropertyFormalReported(place, body);
    }
  }
}

TEST(TypedPropertyFormalParsing,
     DISABLED_ASequenceOrExpressionPositionIsReportedInEachPlace) {
  for (const char* place : kPropertyFormalPlaces) {
    for (const char* body : {"(q) |-> b",
                             "(q) |=> b",
                             "q #-# b",
                             "q #=# b",
                             "q ##1 b",
                             "b ##1 q",
                             "q ##[1:2] b",
                             "b ##[1:2] q",
                             "##1 q",
                             "q intersect b",
                             "b intersect q",
                             "q within b",
                             "b within q",
                             "b throughout q",
                             "q [*2]",
                             "q [=2]",
                             "q [->1]",
                             "strong(q)",
                             "weak(q)",
                             "first_match(q)",
                             "bit v; (q, v = 1) ##1 b",
                             "q && b",
                             "b || q",
                             "!q",
                             "q == b",
                             "if (q) b",
                             "case (q) 1'b1: b; endcase",
                             "accept_on (q) b",
                             "reject_on (q) b",
                             "sync_accept_on (q) b",
                             "sync_reject_on (q) b",
                             "disable iff (q) b",
                             "@(q) b",
                             "$rose(q)",
                             "q.triggered",
                             "q.matched",
                             "s(q)",
                             "st(q)"}) {
      ExpectPropertyFormalReported(place, body);
    }
  }
}

TEST(TypedPropertyFormalParsing, APropertyPositionIsAcceptedInEachPlace) {
  for (const char* place : kPropertyFormalPlaces) {
    for (const char* body : {"q",
                             "b |-> q",
                             "b |=> q",
                             "not q",
                             "q and b",
                             "b or q",
                             "q implies b",
                             "b iff q",
                             "q until b",
                             "b s_until q",
                             "q until_with b",
                             "b s_until_with q",
                             "always q",
                             "s_always [1:2] q",
                             "eventually [1:2] q",
                             "s_eventually q",
                             "nexttime q",
                             "s_nexttime [2] q",
                             "b #-# q",
                             "b #=# q",
                             "if (a) q else b",
                             "case (a) 1'b1: q; default: b; endcase",
                             "accept_on (a) q",
                             "sync_reject_on (a) q",
                             "r(q)"}) {
      SCOPED_TRACE(std::string(place) + " " + body);
      auto r = Parse(PropertyFormalIn(place, body));
      EXPECT_FALSE(r.has_errors);
    }
  }
}

}  // namespace
