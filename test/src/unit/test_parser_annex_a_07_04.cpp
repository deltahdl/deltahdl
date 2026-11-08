#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

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

TEST(SpecifyPathDelayGrammar, NonEnumeratedValueCountRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "path delay must have 1, 2, 3, 6, or 12 values", 3, "30.5"));
}

TEST(SpecifyPathDelayGrammar, ParenthesizedListMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "30.5"));
}

}  // namespace
