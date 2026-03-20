#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- table / endtable keywords ---

TEST(UdpBodyLexing, TableKeyword) {
  auto r = LexOne("table");
  EXPECT_EQ(r.token.kind, TokenKind::kKwTable);
}

TEST(UdpBodyLexing, EndtableKeyword) {
  auto r = LexOne("endtable");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndtable);
}

TEST(UdpBodyLexing, TableSubstringsAreIdentifiers) {
  auto r1 = LexOne("tabl");
  EXPECT_EQ(r1.token.kind, TokenKind::kIdentifier);

  auto r2 = LexOne("tables");
  EXPECT_EQ(r2.token.kind, TokenKind::kIdentifier);

  auto r3 = LexOne("endtabl");
  EXPECT_EQ(r3.token.kind, TokenKind::kIdentifier);

  auto r4 = LexOne("endtables");
  EXPECT_EQ(r4.token.kind, TokenKind::kIdentifier);
}

// --- token sequences for UDP body constructs ---

TEST(UdpBodyLexing, CombinationalEntryTokenSequence) {
  auto tokens = Lex("0 1 : 0 ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(UdpBodyLexing, SequentialEntryTokenSequence) {
  auto tokens = Lex("0 r : ? : 0 ;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kQuestion);
  EXPECT_EQ(tokens[4].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
}

TEST(UdpBodyLexing, InitialStatementTokenSequence) {
  auto tokens = Lex("initial q = 1'b0 ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInitial);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(UdpBodyLexing, ParenthesizedEdgeTokenSequence) {
  auto tokens = Lex("(01)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(UdpBodyLexing, DashAsMinusToken) {
  auto tokens = Lex("? 0 : ? : - ;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[5].kind, TokenKind::kMinus);
}

TEST(UdpBodyLexing, TableEndtableDelimitBodyTokens) {
  auto tokens = Lex("table 0 : 0 ; endtable");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTable);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwEndtable);
}

TEST(UdpBodyLexing, LevelSymbolTokenKinds) {
  auto t0 = LexOne("0");
  EXPECT_EQ(t0.token.kind, TokenKind::kIntLiteral);

  auto t1 = LexOne("1");
  EXPECT_EQ(t1.token.kind, TokenKind::kIntLiteral);

  auto tx = LexOne("x");
  EXPECT_EQ(tx.token.kind, TokenKind::kIdentifier);

  auto tq = LexOne("?");
  EXPECT_EQ(tq.token.kind, TokenKind::kQuestion);

  auto tb = LexOne("b");
  EXPECT_EQ(tb.token.kind, TokenKind::kIdentifier);
}

TEST(UdpBodyLexing, EdgeSymbolTokenKinds) {
  auto tr = LexOne("r");
  EXPECT_EQ(tr.token.kind, TokenKind::kIdentifier);

  auto tf = LexOne("f");
  EXPECT_EQ(tf.token.kind, TokenKind::kIdentifier);

  auto tp = LexOne("p");
  EXPECT_EQ(tp.token.kind, TokenKind::kIdentifier);

  auto tn = LexOne("n");
  EXPECT_EQ(tn.token.kind, TokenKind::kIdentifier);

  auto ts = LexOne("*");
  EXPECT_EQ(ts.token.kind, TokenKind::kStar);
}

}  // namespace
