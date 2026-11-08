#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>

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

}  // namespace
