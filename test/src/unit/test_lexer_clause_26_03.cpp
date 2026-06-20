#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(PackageReferenceLexing, ScopeResolutionOperatorTokenized) {
  auto tokens = Lex("pkg::ident");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "ident");
}

TEST(PackageReferenceLexing, WildcardImportTokenSequence) {
  auto tokens = Lex("pkg::*");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

TEST(PackageReferenceLexing, ImportKeywordTokenized) {
  auto tokens = Lex("import pkg::ident;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwImport);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

}  // namespace
