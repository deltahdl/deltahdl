#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(ToleranceOperatorLexing, ToleranceOperators) {
  auto tokens = Lex("+/- +%-");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusSlashMinus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPercentMinus);
}
