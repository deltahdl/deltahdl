#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(SpecifyBlockDeclLexing, SpecifyKeywordToken) {
  auto r = LexOne("specify");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSpecify);
}

TEST(SpecifyBlockDeclLexing, EndspecifyKeywordToken) {
  auto r = LexOne("endspecify");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndspecify);
}

TEST(SpecifyBlockDeclLexing, SpecifyEndspecifyBracketStream) {
  auto tokens = Lex("specify endspecify");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSpecify);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndspecify);
}

TEST(SpecifyBlockDeclLexing, SpecifyPrefixIsIdentifier) {
  auto tokens = Lex("specifyxx");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "specifyxx");
}

TEST(SpecifyBlockDeclLexing, EndspecifyPrefixIsIdentifier) {
  auto tokens = Lex("endspecify_alt");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "endspecify_alt");
}

}  // namespace
