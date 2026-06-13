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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
