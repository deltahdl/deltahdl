#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LoopGenerateLexing, GenvarKeywordTokenizes) {
  auto tokens = Lex("genvar i;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwGenvar);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "i");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

}  // namespace
