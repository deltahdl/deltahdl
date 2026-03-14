#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §15.5: event is a keyword (unlike semaphore/mailbox which are identifiers).
TEST(NamedEventLexer, EventTokenizesAsKeyword) {
  auto result = LexOne("event");
  EXPECT_EQ(result.token.kind, TokenKind::kKwEvent);
  EXPECT_EQ(result.token.text, "event");
}

// §15.5: event in a declaration context tokenizes correctly.
TEST(NamedEventLexer, EventInDeclarationContext) {
  auto tokens = Lex("event done;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEvent);
  EXPECT_EQ(tokens[0].text, "event");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "done");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

// §15.5: Multiple event declarations in a comma-separated list.
TEST(NamedEventLexer, MultipleEventDeclarationTokens) {
  auto tokens = Lex("event done, blast;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEvent);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "done");
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "blast");
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

}  // namespace
