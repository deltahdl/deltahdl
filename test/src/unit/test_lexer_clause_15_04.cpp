#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §15.4: mailbox is a built-in class, not a keyword token.
// It must tokenize as an identifier so the parser can treat it
// as a named type via the known_types_ mechanism.
TEST(MailboxLexer, MailboxTokenizesAsIdentifier) {
  auto result = LexOne("mailbox");
  EXPECT_EQ(result.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(result.token.text, "mailbox");
}

// §15.4: mailbox in a declaration context tokenizes correctly.
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
