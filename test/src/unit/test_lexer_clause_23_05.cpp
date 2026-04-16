#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- Req 1: extern module token sequence ---

TEST(ExternModuleLexing, ExternModuleTokenSequence) {
  auto tokens = Lex("extern module m");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwExtern);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "m");
}

TEST(ExternModuleLexing, ExternMacromoduleTokenSequence) {
  auto tokens = Lex("extern macromodule m");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwExtern);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwMacromodule);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "m");
}

}  // namespace
