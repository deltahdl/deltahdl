#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §6.8 anchor: the `var` keyword the subclause introduces tokenizes as a
// single keyword token — the parser tests in this clause rely on it.
TEST(VarKeyword, VarTokenizesAsKeyword) {
  auto r = LexOne("var");
  EXPECT_EQ(r.token.kind, TokenKind::kKwVar);
}

// §6.8 BNF `integer_atom_type ::= byte | shortint | int | longint | integer
// | time`. Each atom-type keyword must tokenize as its own keyword kind so
// the parser can distinguish them in a data_type production.
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

// §6.8 BNF `integer_vector_type ::= bit | logic | reg`. Each vector-type
// keyword must tokenize as its own keyword kind.
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

// §6.8 BNF `non_integer_type ::= shortreal | real | realtime`. Each
// non-integer keyword must tokenize as its own keyword kind.
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

// §6.8 BNF `signing ::= signed | unsigned`. Both signing keywords must
// tokenize as distinct keyword kinds so the parser can attach them to a
// data_type or implicit_data_type.
TEST(Signing, SignedTokenizesAsKeyword) {
  auto r = LexOne("signed");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSigned);
}

TEST(Signing, UnsignedTokenizesAsKeyword) {
  auto r = LexOne("unsigned");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUnsigned);
}

}  // namespace
