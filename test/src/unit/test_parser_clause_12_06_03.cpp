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

// §12.6.3: the predicate of a conditional expression may be a whole sequence of
// matches clauses joined by `&&&`, not just one. A three-clause predicate must
// parse into a left-associated `&&&` tree whose left operand is itself a `&&&`,
// confirming the parser accepts more than two predicate clauses in a ternary.
TEST(TernaryMatchesParsing, MatchesChainInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (a matches 8'd1 &&& b matches 8'd2 &&& c) ? 1 : 0;\n"
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
  // The left operand of the outermost `&&&` is itself a `&&&` chain, so the
  // predicate holds three clauses rather than two.
  ASSERT_NE(stmt->rhs->condition->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->condition->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->condition->lhs->op, TokenKind::kAmpAmpAmp);
}

}
