#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- R7: Period character separates hierarchy level names ---

TEST(HierarchicalNameLexing, DotSeparatedPathTokens) {
  auto tokens = Lex("a.b.c");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "b");
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "c");
}

// --- R7: Escaped identifiers in hierarchical paths are followed by
//     whitespace then a period separator ---

TEST(HierarchicalNameLexing, EscapedIdentInHierarchicalPath) {
  auto tokens = Lex("\\esc .b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "b");
}

// --- R13: Instance select brackets appear within hierarchical path tokens ---

TEST(HierarchicalNameLexing, InstanceSelectInPathTokens) {
  auto tokens = Lex("a[0].b");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRBracket);
  EXPECT_EQ(tokens[4].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].text, "b");
}

}  // namespace
