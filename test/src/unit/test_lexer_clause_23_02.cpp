// §23.2

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ModuleDefinitions, ModuleEndmoduleTokenSequence) {
  auto tokens = Lex("module m ; endmodule");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndmodule);
}

TEST(ModuleDefinitions, MacromoduleTokenSequence) {
  auto tokens = Lex("macromodule m ; endmodule");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwMacromodule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndmodule);
}

TEST(ModuleDefinitions, IdentifierAfterModuleKeyword) {
  auto tokens = Lex("module my_design;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "my_design");
}

}  // namespace
