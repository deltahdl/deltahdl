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
// --- §5: Source locations ---
TEST(LexerCh5, SourceLocations) {
  auto tokens = Lex("a\nb c");
  struct Case {
    size_t idx;
    int line;
    int column;
  };
  Case expected[] = {
      {0, 1, 1},
      {1, 2, 1},
      {2, 2, 3},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].loc.line, c.line) << "token " << c.idx;
    EXPECT_EQ(tokens[c.idx].loc.column, c.column) << "token " << c.idx;
  }
}

