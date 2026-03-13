#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §15.3: semaphore is a built-in class, not a keyword token.
// It must tokenize as an identifier so the parser can treat it
// as a named type via the known_types_ mechanism.
TEST(SemaphoreLexer, SemaphoreTokenizesAsIdentifier) {
  auto result = LexOne("semaphore");
  EXPECT_EQ(result.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(result.token.text, "semaphore");
}

// §15.3: semaphore in a declaration context tokenizes correctly.
TEST(SemaphoreLexer, SemaphoreInDeclarationContext) {
  auto tokens = Lex("semaphore smTx;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "semaphore");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "smTx");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

}  // namespace
