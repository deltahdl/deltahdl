#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(VarKeyword, VarTokenizesAsKeyword) {
  auto r = LexOne("var");
  EXPECT_EQ(r.token.kind, TokenKind::kKwVar);
}

TEST(IntegerAtomType, ByteTokenizesAsKeyword) {
  auto r = LexOne("byte");
  EXPECT_EQ(r.token.kind, TokenKind::kKwByte);
}

TEST(IntegerAtomType, ShortintTokenizesAsKeyword) {
  auto r = LexOne("shortint");
  EXPECT_EQ(r.token.kind, TokenKind::kKwShortint);
}

TEST(IntegerAtomType, IntTokenizesAsKeyword) {
  auto r = LexOne("int");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInt);
}

TEST(IntegerAtomType, LongintTokenizesAsKeyword) {
  auto r = LexOne("longint");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLongint);
}

TEST(IntegerAtomType, IntegerTokenizesAsKeyword) {
  auto r = LexOne("integer");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInteger);
}

TEST(IntegerAtomType, TimeTokenizesAsKeyword) {
  auto r = LexOne("time");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTime);
}

TEST(IntegerVectorType, BitTokenizesAsKeyword) {
  auto r = LexOne("bit");
  EXPECT_EQ(r.token.kind, TokenKind::kKwBit);
}

TEST(IntegerVectorType, LogicTokenizesAsKeyword) {
  auto r = LexOne("logic");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLogic);
}

TEST(IntegerVectorType, RegTokenizesAsKeyword) {
  auto r = LexOne("reg");
  EXPECT_EQ(r.token.kind, TokenKind::kKwReg);
}

TEST(NonIntegerType, ShortrealTokenizesAsKeyword) {
  auto r = LexOne("shortreal");
  EXPECT_EQ(r.token.kind, TokenKind::kKwShortreal);
}

TEST(NonIntegerType, RealTokenizesAsKeyword) {
  auto r = LexOne("real");
  EXPECT_EQ(r.token.kind, TokenKind::kKwReal);
}

TEST(NonIntegerType, RealtimeTokenizesAsKeyword) {
  auto r = LexOne("realtime");
  EXPECT_EQ(r.token.kind, TokenKind::kKwRealtime);
}

TEST(Signing, SignedTokenizesAsKeyword) {
  auto r = LexOne("signed");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSigned);
}

TEST(Signing, UnsignedTokenizesAsKeyword) {
  auto r = LexOne("unsigned");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnsigned);
}

}  // namespace
