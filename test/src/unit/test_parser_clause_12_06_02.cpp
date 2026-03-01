// §12.6.2: Pattern matching in if statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// pattern ::= . variable_identifier
// ---------------------------------------------------------------------------
// §12.6: pattern with identifier binding (.name)
TEST(ParserA60701, PatternDotIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= .*
// ---------------------------------------------------------------------------
// §12.6: wildcard pattern .*
TEST(ParserA60701, PatternWildcard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .*) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// expression_or_cond_pattern ::= expression | cond_pattern
// cond_pattern ::= expression matches pattern
// ---------------------------------------------------------------------------
// §12.6: cond_pattern in if condition — expr matches constant
TEST(ParserA606, CondPatternMatchesConstant) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 3) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // condition should be a matches binary expression
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
}

// §12.6: matches with &&& in cond_predicate
TEST(ParserA606, CondPatternMatchesWithTripleAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5 &&& en) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

// ---------------------------------------------------------------------------
// Parsing: matches as binary expression operator
// ---------------------------------------------------------------------------
// §12.6.2: matches operator in if-condition
TEST(ParserA60701, MatchesExprInIfCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
}

// §12.6.2: matches with &&& operator in if-condition
TEST(ParserA60701, MatchesWithTripleAndInIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5 &&& en) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
