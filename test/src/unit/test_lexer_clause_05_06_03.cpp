// §5.6.3: System tasks and system functions

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- §5.6.3: System tasks and system functions ---
TEST(LexerCh50603, EmbeddedDollar) {
  // §5.6.3: system_tf_identifier allows $ within the name.
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

}  // namespace
