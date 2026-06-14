#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(SemaphoreLexer, SemaphoreInDeclarationContext) {
  auto tokens = Lex("semaphore smTx;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "semaphore");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "smTx");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

}
