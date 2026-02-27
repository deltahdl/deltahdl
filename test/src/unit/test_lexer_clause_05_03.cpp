#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §5.3: White space ---

TEST(LexerCh503, VerticalTabIsWhitespace) {
  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}
