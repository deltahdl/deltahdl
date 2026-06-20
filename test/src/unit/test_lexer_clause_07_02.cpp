#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(StructUnionKeywords, StructAndUnionTokenizeDistinctly) {
  auto r1 = LexOne("struct");
  EXPECT_EQ(r1.token.kind, TokenKind::kKwStruct);
  auto r2 = LexOne("union");
  EXPECT_EQ(r2.token.kind, TokenKind::kKwUnion);
}

TEST(StructUnionKeywords, SoftAndTaggedTokenizeDistinctly) {
  auto rs = LexOne("soft");
  EXPECT_EQ(rs.token.kind, TokenKind::kKwSoft);
  auto rt = LexOne("tagged");
  EXPECT_EQ(rt.token.kind, TokenKind::kKwTagged);
}

TEST(StructUnionKeywords, PackedTokenizesAsKeyword) {
  auto r = LexOne("packed");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPacked);
}

TEST(StructUnionKeywords, VoidTokenizesAsKeyword) {
  auto r = LexOne("void");
  EXPECT_EQ(r.token.kind, TokenKind::kKwVoid);
}

}  // namespace
