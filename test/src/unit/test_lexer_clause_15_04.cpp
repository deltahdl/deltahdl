#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(MailboxLexer, MailboxTokenizesAsIdentifier) {
  auto result = LexOne("mailbox");
  EXPECT_EQ(result.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(result.token.text, "mailbox");
}

TEST(MailboxLexer, MailboxInDeclarationContext) {
  auto tokens = Lex("mailbox mbxRcv;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "mailbox");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "mbxRcv");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

}  // namespace
