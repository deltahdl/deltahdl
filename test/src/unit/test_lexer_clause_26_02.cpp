#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(PackageDeclarationLexing, PackageAndEndpackageKeywordsTokenized) {
  auto tokens = Lex("package pkg; endpackage");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPackage);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "pkg");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndpackage);
}

TEST(PackageDeclarationLexing, PackageLifetimeAutomaticTokenized) {
  auto tokens = Lex("package automatic pkg;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPackage);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwAutomatic);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "pkg");
}

TEST(PackageDeclarationLexing, PackageLifetimeStaticTokenized) {
  auto tokens = Lex("package static pkg;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPackage);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwStatic);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "pkg");
}

TEST(PackageDeclarationLexing, EndpackageLabelColonTokenized) {
  auto tokens = Lex("endpackage : pkg");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEndpackage);
  EXPECT_EQ(tokens[1].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "pkg");
}

TEST(PackageDeclarationLexing, AnonymousProgramKeywordsTokenized) {
  auto tokens = Lex("program ; endprogram");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwProgram);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwEndprogram);
}

}  // namespace
