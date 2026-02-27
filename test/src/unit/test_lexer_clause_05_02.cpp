#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

// --- §5.2: Lexical tokens ---

TEST(LexerCh502, EachTokenHasOneOrMoreChars) {
  // §5.2: A lexical token shall consist of one or more characters.
  auto tokens = Lex("module m; logic [7:0] x = 8'hFF + 1; endmodule");
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    EXPECT_GE(tokens[i].text.size(), 1u)
        << "token " << i << " (" << tokens[i].text << ") is empty";
  }
}
