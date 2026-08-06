#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NameSpaceLexing, AttributeNameSpaceDelimitersTokenized) {
  auto tokens = Lex("(* keep *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "keep");
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(NameSpaceLexing, PackageKeywordTokenized) {
  auto tokens = Lex("package my_pkg; endpackage");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPackage);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "my_pkg");
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndpackage);
}

TEST(NameSpaceLexing, DefinitionsNameSpaceKeywordsTokenized) {
  auto tokens = Lex("module primitive program interface");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwPrimitive);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwProgram);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwInterface);
}

}  // namespace
