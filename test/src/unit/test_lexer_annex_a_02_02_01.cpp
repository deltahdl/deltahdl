// §A.2.2.1: lexer-stage coverage of the keyword terminals named in
// integer_atom_type, integer_vector_type, non_integer_type, net_type,
// signing, and struct_union.

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.2.2.1 integer_atom_type ::= byte | shortint | int | longint | integer |
// time — each terminal lexes to its own keyword kind.
TEST(NetAndVariableTypeLexing, ByteKeyword) {
  auto tokens = Lex("byte");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwByte);
}

TEST(NetAndVariableTypeLexing, ShortintKeyword) {
  auto tokens = Lex("shortint");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwShortint);
}

TEST(NetAndVariableTypeLexing, IntKeyword) {
  auto tokens = Lex("int");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInt);
}

TEST(NetAndVariableTypeLexing, LongintKeyword) {
  auto tokens = Lex("longint");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLongint);
}

TEST(NetAndVariableTypeLexing, IntegerKeyword) {
  auto tokens = Lex("integer");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInteger);
}

TEST(NetAndVariableTypeLexing, TimeKeyword) {
  auto tokens = Lex("time");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTime);
}

// §A.2.2.1 integer_vector_type ::= bit | logic | reg
TEST(NetAndVariableTypeLexing, BitKeyword) {
  auto tokens = Lex("bit");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBit);
}

TEST(NetAndVariableTypeLexing, LogicKeyword) {
  auto tokens = Lex("logic");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLogic);
}

TEST(NetAndVariableTypeLexing, RegKeyword) {
  auto tokens = Lex("reg");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwReg);
}

// §A.2.2.1 non_integer_type ::= shortreal | real | realtime
TEST(NetAndVariableTypeLexing, ShortrealKeyword) {
  auto tokens = Lex("shortreal");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwShortreal);
}

TEST(NetAndVariableTypeLexing, RealKeyword) {
  auto tokens = Lex("real");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwReal);
}

TEST(NetAndVariableTypeLexing, RealtimeKeyword) {
  auto tokens = Lex("realtime");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRealtime);
}

// §A.2.2.1 net_type ::= supply0 | supply1 | tri | triand | trior | trireg |
// tri0 | tri1 | uwire | wire | wand | wor — each terminal is a distinct token.
TEST(NetAndVariableTypeLexing, SupplyZeroNetKeyword) {
  auto tokens = Lex("supply0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSupply0);
}

TEST(NetAndVariableTypeLexing, SupplyOneNetKeyword) {
  auto tokens = Lex("supply1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSupply1);
}

TEST(NetAndVariableTypeLexing, TriKeyword) {
  auto tokens = Lex("tri");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTri);
}

TEST(NetAndVariableTypeLexing, TriandKeyword) {
  auto tokens = Lex("triand");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTriand);
}

TEST(NetAndVariableTypeLexing, TriorKeyword) {
  auto tokens = Lex("trior");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTrior);
}

TEST(NetAndVariableTypeLexing, TriregKeyword) {
  auto tokens = Lex("trireg");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTrireg);
}

TEST(NetAndVariableTypeLexing, TriZeroKeyword) {
  auto tokens = Lex("tri0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTri0);
}

TEST(NetAndVariableTypeLexing, TriOneKeyword) {
  auto tokens = Lex("tri1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTri1);
}

TEST(NetAndVariableTypeLexing, UwireKeyword) {
  auto tokens = Lex("uwire");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUwire);
}

TEST(NetAndVariableTypeLexing, WireKeyword) {
  auto tokens = Lex("wire");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWire);
}

TEST(NetAndVariableTypeLexing, WandKeyword) {
  auto tokens = Lex("wand");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWand);
}

TEST(NetAndVariableTypeLexing, WorKeyword) {
  auto tokens = Lex("wor");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWor);
}

// §A.2.2.1 signing ::= signed | unsigned
TEST(NetAndVariableTypeLexing, SignedKeyword) {
  auto tokens = Lex("signed");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSigned);
}

TEST(NetAndVariableTypeLexing, UnsignedKeyword) {
  auto tokens = Lex("unsigned");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUnsigned);
}

// §A.2.2.1 struct_union ::= struct | union [ soft | tagged ]
TEST(NetAndVariableTypeLexing, StructKeyword) {
  auto tokens = Lex("struct");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwStruct);
}

TEST(NetAndVariableTypeLexing, UnionKeyword) {
  auto tokens = Lex("union");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwUnion);
}

TEST(NetAndVariableTypeLexing, TaggedKeyword) {
  auto tokens = Lex("tagged");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTagged);
}

TEST(NetAndVariableTypeLexing, SoftKeyword) {
  auto tokens = Lex("soft");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSoft);
}

// §A.2.2.1 data_type ::= ... | string | chandle | event | void | ...
TEST(NetAndVariableTypeLexing, StringKeyword) {
  auto tokens = Lex("string");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwString);
}

TEST(NetAndVariableTypeLexing, ChandleKeyword) {
  auto tokens = Lex("chandle");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwChandle);
}

TEST(NetAndVariableTypeLexing, EventKeyword) {
  auto tokens = Lex("event");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEvent);
}

TEST(NetAndVariableTypeLexing, VoidKeyword) {
  auto tokens = Lex("void");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwVoid);
}

// §A.2.2.1 var_data_type ::= data_type | var data_type_or_implicit — the `var`
// terminal is a distinct keyword token.
TEST(NetAndVariableTypeLexing, VarKeyword) {
  auto tokens = Lex("var");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwVar);
}

// §A.2.2.1 data_type ::= ... | type_reference — the `type` keyword that opens
// a type_reference is a distinct token from any identifier.
TEST(NetAndVariableTypeLexing, TypeKeyword) {
  auto tokens = Lex("type");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwType);
}

}  // namespace
