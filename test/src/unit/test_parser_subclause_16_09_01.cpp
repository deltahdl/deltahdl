#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/sequence_operator_precedence.h"

using namespace delta;

namespace {

TEST(SequenceOperatorPrecedence, TableOrderStrictlyDescending) {
  const SequenceOperator kOrdered[] = {
      SequenceOperator::kRepetition, SequenceOperator::kCycleDelay,
      SequenceOperator::kThroughout, SequenceOperator::kWithin,
      SequenceOperator::kIntersect,  SequenceOperator::kAnd,
      SequenceOperator::kOr,
  };
  for (size_t i = 1; i < std::size(kOrdered); ++i) {
    EXPECT_GT(SequenceOperatorPrecedence(kOrdered[i - 1]),
              SequenceOperatorPrecedence(kOrdered[i]))
        << "operator at row " << (i - 1) << " must bind tighter than row " << i;
    EXPECT_TRUE(SequenceOperatorBindsTighter(kOrdered[i - 1], kOrdered[i]));
    EXPECT_FALSE(SequenceOperatorBindsTighter(kOrdered[i], kOrdered[i - 1]));
  }
}

TEST(SequenceOperatorPrecedence, AssociativityMatchesTable) {
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kRepetition),
            SequenceOperatorAssoc::kNone);
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kCycleDelay),
            SequenceOperatorAssoc::kLeft);
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kThroughout),
            SequenceOperatorAssoc::kRight);
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kWithin),
            SequenceOperatorAssoc::kLeft);
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kIntersect),
            SequenceOperatorAssoc::kLeft);
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kAnd),
            SequenceOperatorAssoc::kLeft);
  EXPECT_EQ(SequenceOperatorAssociativity(SequenceOperator::kOr),
            SequenceOperatorAssoc::kLeft);
}

TEST(SequenceOperatorPrecedence, TokenMappingForSingleTokenOperators) {
  SequenceOperator op{};
  ASSERT_TRUE(SequenceOperatorFromToken(TokenKind::kHashHash, &op));
  EXPECT_EQ(op, SequenceOperator::kCycleDelay);
  ASSERT_TRUE(SequenceOperatorFromToken(TokenKind::kKwThroughout, &op));
  EXPECT_EQ(op, SequenceOperator::kThroughout);
  ASSERT_TRUE(SequenceOperatorFromToken(TokenKind::kKwWithin, &op));
  EXPECT_EQ(op, SequenceOperator::kWithin);
  ASSERT_TRUE(SequenceOperatorFromToken(TokenKind::kKwIntersect, &op));
  EXPECT_EQ(op, SequenceOperator::kIntersect);
  ASSERT_TRUE(SequenceOperatorFromToken(TokenKind::kKwAnd, &op));
  EXPECT_EQ(op, SequenceOperator::kAnd);
  ASSERT_TRUE(SequenceOperatorFromToken(TokenKind::kKwOr, &op));
  EXPECT_EQ(op, SequenceOperator::kOr);
}

TEST(SequenceOperatorPrecedence, TokenMappingRejectsNonOperator) {
  SequenceOperator op = SequenceOperator::kRepetition;
  EXPECT_FALSE(SequenceOperatorFromToken(TokenKind::kPlus, &op));
  EXPECT_FALSE(SequenceOperatorFromToken(TokenKind::kKwProperty, &op));
}

ParseResult ParseCover(const std::string& body) {
  return Parse(
      "module m;\n  logic clk, a, b;\n  cover property (@(posedge clk) " +
      body + ");\nendmodule\n");
}

TEST(SequenceOperatorPrecedence, ARepetitionLeftOfThroughoutIsReported) {
  auto r = ParseCover("a[*2] throughout b ##1 b");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a sequence stands where the grammar admits only an expression_or_dist",
      3, "A.2.10"));
}

TEST(SequenceOperatorPrecedence, ARepetitionRightOfThroughoutIsAccepted) {
  auto r = ParseCover("a throughout b[*2]");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceOperatorPrecedence, ABracketDirectlyAfterABracketIsReported) {
  for (const char* body : {"a[*2][*3]", "a[=2][*2]", "a[->1][*2]"}) {
    SCOPED_TRACE(body);
    auto r = ParseCover(body);
    EXPECT_TRUE(
        ReportedError(r.diags, "is not one the grammar admits", 3, "A.2.10"));
  }
}

TEST(SequenceOperatorPrecedence, AParenthesizedRepetitionTakesABracket) {
  for (const char* body : {"(a[*2])[*3]", "(a[=2])[*2]", "(a[->1])[*2]"}) {
    SCOPED_TRACE(body);
    auto r = ParseCover(body);
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
