

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

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

TEST(NetAndVariableTypeLexing, VarKeyword) {
  auto tokens = Lex("var");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwVar);
}

TEST(NetAndVariableTypeLexing, TypeKeyword) {
  auto tokens = Lex("type");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwType);
}

TEST(NetAndVariableTypeLexing, InterconnectKeyword) {
  auto tokens = Lex("interconnect");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInterconnect);
}

TEST(NetAndVariableTypeLexing, InterfaceKeyword) {
  auto tokens = Lex("interface");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInterface);
}

TEST(NetAndVariableTypeLexing, VirtualKeyword) {
  auto tokens = Lex("virtual");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwVirtual);
}

TEST(NetAndVariableTypeLexing, PackedKeyword) {
  auto tokens = Lex("packed");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwPacked);
}

TEST(NetAndVariableTypeLexing, ConstKeyword) {
  auto tokens = Lex("const");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwConst);
}

TEST(NetAndVariableTypeLexing, EnumKeyword) {
  auto tokens = Lex("enum");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwEnum);
}

TEST(NetAndVariableTypeLexing, ConstantPrimaryCastUsesApostropheToken) {
  // 5'(x) — the constant_primary alternative of casting_type. The bare digit
  // must lex as an integer literal and the apostrophe as its own token so the
  // parser can build the cast; an eager sized-literal pass would mis-tokenize
  // the parenthesis as a base letter.
  auto tokens = Lex("5'(x)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "5");
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostrophe);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
}

TEST(NetAndVariableTypeLexing, SizedLiteralStillLexesAsOneToken) {
  // The lookahead must not break sized literals such as 4'd5 — the apostrophe
  // followed by a base letter still folds into one kIntLiteral token.
  auto tokens = Lex("4'd5");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4'd5");
}

}  // namespace
