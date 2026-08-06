#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(IndexedPartSelectLexing, IndexedPartSelectOperators) {
  auto tokens = Lex("+: -:");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusColon);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusColon);
}
