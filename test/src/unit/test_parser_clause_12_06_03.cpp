#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TernaryMatchesParsing, MatchesInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (x matches 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
  ASSERT_NE(stmt->rhs->condition, nullptr);
  EXPECT_EQ(stmt->rhs->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->condition->op, TokenKind::kKwMatches);
}

TEST(TernaryMatchesParsing, MatchesWithGuardInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (x matches 5 &&& en) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
  ASSERT_NE(stmt->rhs->condition, nullptr);
  EXPECT_EQ(stmt->rhs->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->condition->op, TokenKind::kAmpAmpAmp);
}

TEST(TernaryMatchesParsing, MatchesWildcardInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (sel matches 4'bx1x0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
