

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ProgramBlockLexing, ProgramKeywordRecognised) {
  auto r = LexOne("program");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProgram);
}

TEST(ProgramBlockLexing, EndprogramKeywordRecognised) {
  auto r = LexOne("endprogram");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndprogram);
}

TEST(ProgramBlockLexing, ProgramEnclosureTokenStream) {
  auto tokens = Lex("program p; endprogram");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwProgram);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "p");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndprogram);
}

}  // namespace
