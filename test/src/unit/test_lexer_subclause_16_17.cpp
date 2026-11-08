#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ExpectStatementLexing, ExpectKeywordRoundTrip) {
  auto tokens = Lex("expect");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwExpect);
}

TEST(ExpectStatementLexing, ExpectKeywordIsNotAPrefixMatch) {
  auto tokens = Lex("expected");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

}  // namespace
