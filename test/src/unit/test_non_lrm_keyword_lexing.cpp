

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(GateKeywordLexing, MultipleNInputKeywordsInSequence) {
  auto tokens = Lex("and nand or nor xor xnor");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAnd);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwNand);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwOr);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwNor);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwXor);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwXnor);
}

}  // namespace
