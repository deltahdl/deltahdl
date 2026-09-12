// Annex A.7.4 "Specify path delays" — parser-stage grammar coverage.
//
// §A.7.4 is pure BNF (no 'shall', no other declarative requirements). Every
// production is applied by Parser::ParsePathDelays in parser_specify.cpp, which
// builds the SpecifyPathDecl::delays vector. These tests observe that
// production code applying each grammar rule:
//
//   path_delay_value ::= list_of_path_delay_expressions
//                      | ( list_of_path_delay_expressions )
//   list_of_path_delay_expressions ::= 1- / 2- / 3- / 6- / 12-value forms
//   t*_path_delay_expression ::= path_delay_expression
//   path_delay_expression ::= constant_mintypmax_expression   (DEP §A.8.3)

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Returns the delays vector of the first path declaration in the first
// specify block of the first module, or nullptr if none is present.
const std::vector<Expr*>* FirstPathDelays(CompilationUnit* cu) {
  if (cu == nullptr || cu->modules.empty()) return nullptr;
  for (auto* item : cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) return &si->path.delays;
    }
  }
  return nullptr;
}

// path_delay_value ::= list_of_path_delay_expressions  (bare, unparenthesized)
// list_of_path_delay_expressions ::= t_path_delay_expression
TEST(SpecifyPathDelayGrammar, SingleDelayValueUnparenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  ASSERT_EQ(delays->size(), 1u);
  EXPECT_NE((*delays)[0], nullptr);
}

// path_delay_value ::= ( list_of_path_delay_expressions )  with a 1-value list.
TEST(SpecifyPathDelayGrammar, SingleDelayValueParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (5);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 1u);
}

// list_of_path_delay_expressions ::=
//   trise_path_delay_expression , tfall_path_delay_expression
TEST(SpecifyPathDelayGrammar, RiseFallTwoValues) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 2u);
}

// list_of_path_delay_expressions ::=
//   trise_ , tfall_ , tz_path_delay_expression
TEST(SpecifyPathDelayGrammar, RiseFallZThreeValues) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (3, 5, 7);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 3u);
}

// list_of_path_delay_expressions ::= the 6-value form
//   t01_ , t10_ , t0z_ , tz1_ , tz0_ , t1z_path_delay_expression
TEST(SpecifyPathDelayGrammar, SixValues) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 6u);
}

// list_of_path_delay_expressions ::= the 12-value form
//   t01_ , t10_ , t0z_ , tz1_ , tz0_ , t1z_ , t0x_ , tx1_ , t1x_ , tx0_ ,
//   txz_ , tzx_path_delay_expression
TEST(SpecifyPathDelayGrammar, TwelveValues) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 12u);
}

// path_delay_expression ::= constant_mintypmax_expression. A min:typ:max
// element is parsed as a kMinTypMax expression (machinery from §A.8.3).
TEST(SpecifyPathDelayGrammar, MinTypMaxPathDelayExpression) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  ASSERT_EQ(delays->size(), 1u);
  ASSERT_NE((*delays)[0], nullptr);
  EXPECT_EQ((*delays)[0]->kind, ExprKind::kMinTypMax);
}

// path_delay_value ::= list_of_path_delay_expressions, the bare alternative,
// admits every list form the parenthesized one does: §30.5 has "one or more
// delay values" on the right-hand side and "the delay values may be optionally
// enclosed in a pair of parentheses". A rise and fall pair written without the
// parentheses is read as two delays.
TEST(SpecifyPathDelayGrammar, RiseFallTwoValuesUnparenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 3, 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 2u);
}

// The bare three-value form, each value a constant_mintypmax_expression: the
// colons inside a value and the commas between values are read apart.
TEST(SpecifyPathDelayGrammar, MinTypMaxThreeValuesUnparenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3, 4:5:6, 7:8:9;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  ASSERT_EQ(delays->size(), 3u);
  for (const auto* delay : *delays) {
    ASSERT_NE(delay, nullptr);
    EXPECT_EQ(delay->kind, ExprKind::kMinTypMax);
  }
}

// The bare twelve-value form.
TEST(SpecifyPathDelayGrammar, TwelveValuesUnparenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  EXPECT_EQ(delays->size(), 12u);
}

// A '(' after the '=' opens the parenthesized path_delay_value only where the
// ')' that answers it ends the value; otherwise it opens the first
// constant_mintypmax_expression of the bare list, as in `(1) + 2`, which is
// one delay of value 3 and no parenthesized list of one followed by `+ 2`.
TEST(SpecifyPathDelayGrammar, ParenthesizedOperandOpensBareSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1) + 2;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  ASSERT_EQ(delays->size(), 1u);
  ASSERT_NE((*delays)[0], nullptr);
  EXPECT_EQ((*delays)[0]->kind, ExprKind::kBinary);
}

// The same '(' at the head of a bare list of two: `(2) * 3, (4) + 1` is a rise
// delay and a fall delay, each a binary expression over a parenthesized
// operand.
TEST(SpecifyPathDelayGrammar, ParenthesizedOperandOpensBareList) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (2) * 3, (4) + 1;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const auto* delays = FirstPathDelays(r.cu);
  ASSERT_NE(delays, nullptr);
  ASSERT_EQ(delays->size(), 2u);
  for (const auto* delay : *delays) {
    ASSERT_NE(delay, nullptr);
    EXPECT_EQ(delay->kind, ExprKind::kBinary);
  }
}

// The closed set of list lengths holds for the bare alternative as for the
// parenthesized one: four values without parentheses are rejected at the
// first, where the value begins.
TEST(SpecifyPathDelayGrammar, NonEnumeratedValueCountUnparenthesizedRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = 1, 2, 3, 4;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "path delay must have 1, 2, 3, 6, or 12 values", 3, "30.5"));
}

// The list_of_path_delay_expressions alternatives form a closed set: only 1, 2,
// 3, 6, or 12 expressions are accepted. A 4-value list is not a valid
// alternative and is rejected.
TEST(SpecifyPathDelayGrammar, NonEnumeratedValueCountRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  // §30.5 owns the path delay value count; the report stands at the '(' that
  // opens the list.
  EXPECT_TRUE(ReportedError(
      r.diags, "path delay must have 1, 2, 3, 6, or 12 values", 3, "30.5"));
}

// The parenthesized path_delay_value alternative,
// ( list_of_path_delay_expressions ), requires its closing parenthesis. A list
// opened with '(' but never closed is rejected.
TEST(SpecifyPathDelayGrammar, ParenthesizedListMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2;\n"
      "  endspecify\n"
      "endmodule\n");
  // §30.5 owns the parenthesized path_delay_value.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "30.5"));
}

}  // namespace
