#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(LexerCh502, EachTokenHasOneOrMoreChars) {

  auto tokens = Lex("module m; logic [7:0] x = 8'hFF + 1; endmodule");
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    EXPECT_GE(tokens[i].text.size(), 1u)
        << "token " << i << " (" << tokens[i].text << ") is empty";
  }
}
