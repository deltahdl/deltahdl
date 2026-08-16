#include <gtest/gtest.h>

#include "fixture_lexer.h"

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

// §5.6 makes a simple identifier any sequence of letters, digits, dollar
// signs and underscores, so "specifyxx" is one identifier and not the §30.3
// keyword `specify` followed by anything. This fails if Lexer::LexIdentifier()
// stops the run early or looks the keyword up against a prefix of it: either
// leaves tokens[0] holding kKwSpecify, or holding kIdentifier over the text
// "specify" alone.
TEST(SpecifyBlockDeclLexing, SpecifyPrefixIsIdentifier) {
  auto tokens = Lex("specifyxx");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "specifyxx");
}

// The same §5.6 rule over the underscore, which continues an identifier
// rather than ending it, so "endspecify_alt" is one identifier and not the
// §30.3 keyword `endspecify`. This fails if tokens[0] comes back as
// kKwEndspecify, or as an identifier whose text is any shorter run.
TEST(SpecifyBlockDeclLexing, EndspecifyPrefixIsIdentifier) {
  auto tokens = Lex("endspecify_alt");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "endspecify_alt");
}

}  // namespace
