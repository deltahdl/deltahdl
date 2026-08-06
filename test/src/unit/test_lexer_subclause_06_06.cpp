#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NetTypeKeywords, WireTokenizesAsKeyword) {
  auto r = LexOne("wire");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWire);
}

TEST(NetTypeKeywords, TriTokenizesAsKeyword) {
  auto r = LexOne("tri");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTri);
}

TEST(NetTypeKeywords, Tri0TokenizesAsKeyword) {
  auto r = LexOne("tri0");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTri0);
}

TEST(NetTypeKeywords, Tri1TokenizesAsKeyword) {
  auto r = LexOne("tri1");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTri1);
}

TEST(NetTypeKeywords, TriandTokenizesAsKeyword) {
  auto r = LexOne("triand");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTriand);
}

TEST(NetTypeKeywords, TriorTokenizesAsKeyword) {
  auto r = LexOne("trior");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTrior);
}

TEST(NetTypeKeywords, TriregTokenizesAsKeyword) {
  auto r = LexOne("trireg");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTrireg);
}

TEST(NetTypeKeywords, WandTokenizesAsKeyword) {
  auto r = LexOne("wand");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWand);
}

TEST(NetTypeKeywords, WorTokenizesAsKeyword) {
  auto r = LexOne("wor");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWor);
}

TEST(NetTypeKeywords, Supply0TokenizesAsKeyword) {
  auto r = LexOne("supply0");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSupply0);
}

TEST(NetTypeKeywords, Supply1TokenizesAsKeyword) {
  auto r = LexOne("supply1");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSupply1);
}

TEST(NetTypeKeywords, UwireTokenizesAsKeyword) {
  auto r = LexOne("uwire");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUwire);
}

}  // namespace
