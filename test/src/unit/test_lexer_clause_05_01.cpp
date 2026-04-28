#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, EmptySourceProducesOnlyEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

}  // namespace
