#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(UnionKeywords, UnionLexesAsKeyword) {
  auto r = LexOne("union");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnion);
}

TEST(UnionKeywords, SoftLexesAsKeyword) {
  auto r = LexOne("soft");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSoft);
}

TEST(UnionKeywords, TaggedLexesAsKeyword) {
  auto r = LexOne("tagged");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTagged);
}

TEST(UnionKeywords, PackedLexesAsKeyword) {
  auto r = LexOne("packed");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPacked);
}

TEST(UnionKeywords, VoidLexesAsKeyword) {
  auto r = LexOne("void");
  EXPECT_EQ(r.token.kind, TokenKind::kKwVoid);
}

TEST(UnionKeywords, UnionDeclarationTokenSequence) {
  auto tokens = Lex("union soft { int a; }");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUnion);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwSoft);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwInt);
}

TEST(UnionKeywords, TaggedUnionTokenSequence) {
  auto tokens = Lex("union tagged { void None; int A; }");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUnion);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwTagged);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwVoid);
}

}  // namespace
