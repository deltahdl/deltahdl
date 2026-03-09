#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_5_SingleCharPlus) {
  auto r = LexOne("+");
  EXPECT_EQ(r.token.kind, TokenKind::kPlus);
  EXPECT_EQ(r.token.text.size(), 1u);
}

TEST(LexerClause05, Cl5_5_SingleCharMinus) {
  auto r = LexOne("-");
  EXPECT_EQ(r.token.kind, TokenKind::kMinus);
  EXPECT_EQ(r.token.text.size(), 1u);
}

TEST(LexerClause05, Cl5_5_SingleCharStar) {
  auto r = LexOne("* ");
  EXPECT_EQ(r.token.kind, TokenKind::kStar);
  EXPECT_EQ(r.token.text.size(), 1u);
}

TEST(LexerClause05, Cl5_5_SingleCharSlash) {
  auto tokens = Lex("a / b");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[1].text.size(), 1u);
}

TEST(LexerClause05, Cl5_5_SingleCharPercent) {
  auto r = LexOne("%");
  EXPECT_EQ(r.token.kind, TokenKind::kPercent);
}

TEST(LexerClause05, Cl5_5_SingleCharAmp) {
  auto r = LexOne("& ");
  EXPECT_EQ(r.token.kind, TokenKind::kAmp);
}

TEST(LexerClause05, Cl5_5_SingleCharPipe) {
  auto r = LexOne("| ");
  EXPECT_EQ(r.token.kind, TokenKind::kPipe);
}

TEST(LexerClause05, Cl5_5_SingleCharCaret) {
  auto r = LexOne("^ ");
  EXPECT_EQ(r.token.kind, TokenKind::kCaret);
}

TEST(LexerClause05, Cl5_5_SingleCharTilde) {
  auto r = LexOne("~ ");
  EXPECT_EQ(r.token.kind, TokenKind::kTilde);
}

TEST(LexerClause05, Cl5_5_SingleCharBang) {
  auto r = LexOne("! ");
  EXPECT_EQ(r.token.kind, TokenKind::kBang);
}

TEST(LexerClause05, Cl5_5_SingleCharLt) {
  auto r = LexOne("< ");
  EXPECT_EQ(r.token.kind, TokenKind::kLt);
}

TEST(LexerClause05, Cl5_5_SingleCharGt) {
  auto r = LexOne("> ");
  EXPECT_EQ(r.token.kind, TokenKind::kGt);
}

TEST(LexerClause05, Cl5_5_SingleCharQuestion) {
  auto r = LexOne("?");
  EXPECT_EQ(r.token.kind, TokenKind::kQuestion);
}

TEST(LexerClause05, Cl5_5_SingleCharEq) {
  auto r = LexOne("= ");
  EXPECT_EQ(r.token.kind, TokenKind::kEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharPower) {
  auto r = LexOne("**");
  EXPECT_EQ(r.token.kind, TokenKind::kPower);
  EXPECT_EQ(r.token.text.size(), 2u);
}

TEST(LexerClause05, Cl5_5_DoubleCharTildeAmp) {
  auto r = LexOne("~&");
  EXPECT_EQ(r.token.kind, TokenKind::kTildeAmp);
}

TEST(LexerClause05, Cl5_5_DoubleCharTildePipe) {
  auto r = LexOne("~|");
  EXPECT_EQ(r.token.kind, TokenKind::kTildePipe);
}

TEST(LexerClause05, Cl5_5_DoubleCharTildeCaret) {
  auto r = LexOne("~^");
  EXPECT_EQ(r.token.kind, TokenKind::kTildeCaret);
}

TEST(LexerClause05, Cl5_5_DoubleCharCaretTilde) {
  auto r = LexOne("^~");
  EXPECT_EQ(r.token.kind, TokenKind::kCaretTilde);
}

TEST(LexerClause05, Cl5_5_DoubleCharAmpAmp) {
  auto r = LexOne("&&");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpAmp);
}

TEST(LexerClause05, Cl5_5_DoubleCharPipePipe) {
  auto r = LexOne("||");
  EXPECT_EQ(r.token.kind, TokenKind::kPipePipe);
}

TEST(LexerClause05, Cl5_5_DoubleCharEqEq) {
  auto r = LexOne("== ");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharBangEq) {
  auto r = LexOne("!= ");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharLtEq) {
  auto r = LexOne("<= ");
  EXPECT_EQ(r.token.kind, TokenKind::kLtEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharGtEq) {
  auto r = LexOne(">= ");
  EXPECT_EQ(r.token.kind, TokenKind::kGtEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharLtLt) {
  auto r = LexOne("<< ");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLt);
}

TEST(LexerClause05, Cl5_5_DoubleCharGtGt) {
  auto r = LexOne(">> ");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGt);
}

TEST(LexerClause05, Cl5_5_DoubleCharPlusPlus) {
  auto r = LexOne("++");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusPlus);
}

TEST(LexerClause05, Cl5_5_DoubleCharMinusMinus) {
  auto r = LexOne("--");
  EXPECT_EQ(r.token.kind, TokenKind::kMinusMinus);
}

TEST(LexerClause05, Cl5_5_DoubleCharPlusEq) {
  auto r = LexOne("+=");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharMinusEq) {
  auto r = LexOne("-=");
  EXPECT_EQ(r.token.kind, TokenKind::kMinusEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharStarEq) {
  auto r = LexOne("*=");
  EXPECT_EQ(r.token.kind, TokenKind::kStarEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharSlashEq) {
  auto r = LexOne("/=");
  EXPECT_EQ(r.token.kind, TokenKind::kSlashEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharPercentEq) {
  auto r = LexOne("%=");
  EXPECT_EQ(r.token.kind, TokenKind::kPercentEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharAmpEq) {
  auto r = LexOne("&=");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharPipeEq) {
  auto r = LexOne("|=");
  EXPECT_EQ(r.token.kind, TokenKind::kPipeEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharCaretEq) {
  auto r = LexOne("^=");
  EXPECT_EQ(r.token.kind, TokenKind::kCaretEq);
}

TEST(LexerClause05, Cl5_5_DoubleCharArrow) {
  auto r = LexOne("->");
  EXPECT_EQ(r.token.kind, TokenKind::kArrow);
}

TEST(LexerClause05, Cl5_5_DoubleCharEqGt) {
  auto r = LexOne("=>");
  EXPECT_EQ(r.token.kind, TokenKind::kEqGt);
}

TEST(LexerClause05, Cl5_5_DoubleCharStarGt) {
  auto r = LexOne("*>");
  EXPECT_EQ(r.token.kind, TokenKind::kStarGt);
}

TEST(LexerClause05, Cl5_5_DoubleCharHashHash) {
  auto r = LexOne("##");
  EXPECT_EQ(r.token.kind, TokenKind::kHashHash);
}

TEST(LexerClause05, Cl5_5_DoubleCharColonColon) {
  auto r = LexOne("::");
  EXPECT_EQ(r.token.kind, TokenKind::kColonColon);
}

TEST(LexerClause05, Cl5_5_DoubleCharAtAt) {
  auto r = LexOne("@@");
  EXPECT_EQ(r.token.kind, TokenKind::kAtAt);
}

TEST(LexerClause05, Cl5_5_DoubleCharDotStar) {
  auto r = LexOne(".*");
  EXPECT_EQ(r.token.kind, TokenKind::kDotStar);
}

TEST(LexerClause05, Cl5_5_TripleCharEqEqEq) {
  auto r = LexOne("===");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEqEq);
  EXPECT_EQ(r.token.text.size(), 3u);
}

TEST(LexerClause05, Cl5_5_TripleCharBangEqEq) {
  auto r = LexOne("!==");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEqEq);
}

TEST(LexerClause05, Cl5_5_TripleCharEqEqQuestion) {
  auto r = LexOne("==?");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEqQuestion);
}

TEST(LexerClause05, Cl5_5_TripleCharBangEqQuestion) {
  auto r = LexOne("!=?");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEqQuestion);
}

TEST(LexerClause05, Cl5_5_TripleCharLtLtLt) {
  auto r = LexOne("<<<");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLtLt);
}

TEST(LexerClause05, Cl5_5_TripleCharGtGtGt) {
  auto r = LexOne(">>>");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGtGt);
}

TEST(LexerClause05, Cl5_5_TripleCharLtLtEq) {
  auto r = LexOne("<<=");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLtEq);
}

TEST(LexerClause05, Cl5_5_TripleCharGtGtEq) {
  auto r = LexOne(">>=");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGtEq);
}

TEST(LexerClause05, Cl5_5_TripleCharAmpAmpAmp) {
  auto r = LexOne("&&&");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpAmpAmp);
}

TEST(LexerClause05, Cl5_5_TripleCharPipeDashGt) {
  auto r = LexOne("|->");
  EXPECT_EQ(r.token.kind, TokenKind::kPipeDashGt);
}

TEST(LexerClause05, Cl5_5_TripleCharPipeEqGt) {
  auto r = LexOne("|=>");
  EXPECT_EQ(r.token.kind, TokenKind::kPipeEqGt);
}

TEST(LexerClause05, Cl5_5_TripleCharLtDashGt) {
  auto r = LexOne("<->");
  EXPECT_EQ(r.token.kind, TokenKind::kLtDashGt);
}

TEST(LexerClause05, Cl5_5_TripleCharHashMinusHash) {
  auto r = LexOne("#-#");
  EXPECT_EQ(r.token.kind, TokenKind::kHashMinusHash);
}

TEST(LexerClause05, Cl5_5_TripleCharHashEqHash) {
  auto r = LexOne("#=#");
  EXPECT_EQ(r.token.kind, TokenKind::kHashEqHash);
}

TEST(LexerClause05, Cl5_5_TripleCharDashGtGt) {
  auto r = LexOne("->>");
  EXPECT_EQ(r.token.kind, TokenKind::kDashGtGt);
}

TEST(LexerClause05, Cl5_5_TripleCharPlusSlashMinus) {
  auto r = LexOne("+/-");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusSlashMinus);
}

TEST(LexerClause05, Cl5_5_TripleCharPlusPercentMinus) {
  auto r = LexOne("+%-");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusPercentMinus);
}

TEST(LexerClause05, Cl5_5_QuadCharLtLtLtEq) {
  auto r = LexOne("<<<=");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLtLtEq);
}

TEST(LexerClause05, Cl5_5_QuadCharGtGtGtEq) {
  auto r = LexOne(">>>=");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGtGtEq);
}

TEST(LexerClause05, Cl5_5_OperatorsAdjacentToIdentifiers) {
  auto tokens = Lex("a+b*c-d");
  ASSERT_EQ(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_5_MaximalMunchForOperators) {
  auto tokens = Lex("a===b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_5_DoubleNotTriple) {
  auto tokens = Lex("a == b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEq);
}

}
