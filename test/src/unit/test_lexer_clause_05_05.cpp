#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, SingleCharPlus) {
  auto r = LexOne("+");
  EXPECT_EQ(r.token.kind, TokenKind::kPlus);
  EXPECT_EQ(r.token.text.size(), 1u);
}

TEST(LexicalConventionLexing, SingleCharMinus) {
  auto r = LexOne("-");
  EXPECT_EQ(r.token.kind, TokenKind::kMinus);
  EXPECT_EQ(r.token.text.size(), 1u);
}

TEST(LexicalConventionLexing, SingleCharStar) {
  auto r = LexOne("* ");
  EXPECT_EQ(r.token.kind, TokenKind::kStar);
  EXPECT_EQ(r.token.text.size(), 1u);
}

TEST(LexicalConventionLexing, SingleCharSlash) {
  auto tokens = Lex("a / b");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[1].text.size(), 1u);
}

TEST(LexicalConventionLexing, SingleCharPercent) {
  auto r = LexOne("%");
  EXPECT_EQ(r.token.kind, TokenKind::kPercent);
}

TEST(LexicalConventionLexing, SingleCharAmp) {
  auto r = LexOne("& ");
  EXPECT_EQ(r.token.kind, TokenKind::kAmp);
}

TEST(LexicalConventionLexing, SingleCharPipe) {
  auto r = LexOne("| ");
  EXPECT_EQ(r.token.kind, TokenKind::kPipe);
}

TEST(LexicalConventionLexing, SingleCharCaret) {
  auto r = LexOne("^ ");
  EXPECT_EQ(r.token.kind, TokenKind::kCaret);
}

TEST(LexicalConventionLexing, SingleCharTilde) {
  auto r = LexOne("~ ");
  EXPECT_EQ(r.token.kind, TokenKind::kTilde);
}

TEST(LexicalConventionLexing, SingleCharBang) {
  auto r = LexOne("! ");
  EXPECT_EQ(r.token.kind, TokenKind::kBang);
}

TEST(LexicalConventionLexing, SingleCharLt) {
  auto r = LexOne("< ");
  EXPECT_EQ(r.token.kind, TokenKind::kLt);
}

TEST(LexicalConventionLexing, SingleCharGt) {
  auto r = LexOne("> ");
  EXPECT_EQ(r.token.kind, TokenKind::kGt);
}

TEST(LexicalConventionLexing, SingleCharQuestion) {
  auto r = LexOne("?");
  EXPECT_EQ(r.token.kind, TokenKind::kQuestion);
}

TEST(LexicalConventionLexing, SingleCharEq) {
  auto r = LexOne("= ");
  EXPECT_EQ(r.token.kind, TokenKind::kEq);
}

TEST(LexicalConventionLexing, DoubleCharPower) {
  auto r = LexOne("**");
  EXPECT_EQ(r.token.kind, TokenKind::kPower);
  EXPECT_EQ(r.token.text.size(), 2u);
}

TEST(LexicalConventionLexing, DoubleCharTildeAmp) {
  auto r = LexOne("~&");
  EXPECT_EQ(r.token.kind, TokenKind::kTildeAmp);
}

TEST(LexicalConventionLexing, DoubleCharTildePipe) {
  auto r = LexOne("~|");
  EXPECT_EQ(r.token.kind, TokenKind::kTildePipe);
}

TEST(LexicalConventionLexing, DoubleCharTildeCaret) {
  auto r = LexOne("~^");
  EXPECT_EQ(r.token.kind, TokenKind::kTildeCaret);
}

TEST(LexicalConventionLexing, DoubleCharCaretTilde) {
  auto r = LexOne("^~");
  EXPECT_EQ(r.token.kind, TokenKind::kCaretTilde);
}

TEST(LexicalConventionLexing, DoubleCharAmpAmp) {
  auto r = LexOne("&&");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpAmp);
}

TEST(LexicalConventionLexing, DoubleCharPipePipe) {
  auto r = LexOne("||");
  EXPECT_EQ(r.token.kind, TokenKind::kPipePipe);
}

TEST(LexicalConventionLexing, DoubleCharEqEq) {
  auto r = LexOne("== ");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEq);
}

TEST(LexicalConventionLexing, DoubleCharBangEq) {
  auto r = LexOne("!= ");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEq);
}

TEST(LexicalConventionLexing, DoubleCharLtEq) {
  auto r = LexOne("<= ");
  EXPECT_EQ(r.token.kind, TokenKind::kLtEq);
}

TEST(LexicalConventionLexing, DoubleCharGtEq) {
  auto r = LexOne(">= ");
  EXPECT_EQ(r.token.kind, TokenKind::kGtEq);
}

TEST(LexicalConventionLexing, DoubleCharLtLt) {
  auto r = LexOne("<< ");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLt);
}

TEST(LexicalConventionLexing, DoubleCharGtGt) {
  auto r = LexOne(">> ");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGt);
}

TEST(LexicalConventionLexing, DoubleCharPlusPlus) {
  auto r = LexOne("++");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusPlus);
}

TEST(LexicalConventionLexing, DoubleCharMinusMinus) {
  auto r = LexOne("--");
  EXPECT_EQ(r.token.kind, TokenKind::kMinusMinus);
}

TEST(LexicalConventionLexing, DoubleCharPlusEq) {
  auto r = LexOne("+=");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusEq);
}

TEST(LexicalConventionLexing, DoubleCharMinusEq) {
  auto r = LexOne("-=");
  EXPECT_EQ(r.token.kind, TokenKind::kMinusEq);
}

TEST(LexicalConventionLexing, DoubleCharStarEq) {
  auto r = LexOne("*=");
  EXPECT_EQ(r.token.kind, TokenKind::kStarEq);
}

TEST(LexicalConventionLexing, DoubleCharSlashEq) {
  auto r = LexOne("/=");
  EXPECT_EQ(r.token.kind, TokenKind::kSlashEq);
}

TEST(LexicalConventionLexing, DoubleCharPercentEq) {
  auto r = LexOne("%=");
  EXPECT_EQ(r.token.kind, TokenKind::kPercentEq);
}

TEST(LexicalConventionLexing, DoubleCharAmpEq) {
  auto r = LexOne("&=");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpEq);
}

TEST(LexicalConventionLexing, DoubleCharPipeEq) {
  auto r = LexOne("|=");
  EXPECT_EQ(r.token.kind, TokenKind::kPipeEq);
}

TEST(LexicalConventionLexing, DoubleCharCaretEq) {
  auto r = LexOne("^=");
  EXPECT_EQ(r.token.kind, TokenKind::kCaretEq);
}

TEST(LexicalConventionLexing, DoubleCharArrow) {
  auto r = LexOne("->");
  EXPECT_EQ(r.token.kind, TokenKind::kArrow);
}

TEST(LexicalConventionLexing, DoubleCharEqGt) {
  auto r = LexOne("=>");
  EXPECT_EQ(r.token.kind, TokenKind::kEqGt);
}

TEST(LexicalConventionLexing, DoubleCharStarGt) {
  auto r = LexOne("*>");
  EXPECT_EQ(r.token.kind, TokenKind::kStarGt);
}

TEST(LexicalConventionLexing, DoubleCharHashHash) {
  auto r = LexOne("##");
  EXPECT_EQ(r.token.kind, TokenKind::kHashHash);
}

TEST(LexicalConventionLexing, DoubleCharColonColon) {
  auto r = LexOne("::");
  EXPECT_EQ(r.token.kind, TokenKind::kColonColon);
}

TEST(LexicalConventionLexing, DoubleCharAtAt) {
  auto r = LexOne("@@");
  EXPECT_EQ(r.token.kind, TokenKind::kAtAt);
}

TEST(LexicalConventionLexing, DoubleCharDotStar) {
  auto r = LexOne(".*");
  EXPECT_EQ(r.token.kind, TokenKind::kDotStar);
}

TEST(LexicalConventionLexing, TripleCharEqEqEq) {
  auto r = LexOne("===");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEqEq);
  EXPECT_EQ(r.token.text.size(), 3u);
}

TEST(LexicalConventionLexing, TripleCharBangEqEq) {
  auto r = LexOne("!==");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEqEq);
}

TEST(LexicalConventionLexing, TripleCharEqEqQuestion) {
  auto r = LexOne("==?");
  EXPECT_EQ(r.token.kind, TokenKind::kEqEqQuestion);
}

TEST(LexicalConventionLexing, TripleCharBangEqQuestion) {
  auto r = LexOne("!=?");
  EXPECT_EQ(r.token.kind, TokenKind::kBangEqQuestion);
}

TEST(LexicalConventionLexing, TripleCharLtLtLt) {
  auto r = LexOne("<<<");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLtLt);
}

TEST(LexicalConventionLexing, TripleCharGtGtGt) {
  auto r = LexOne(">>>");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGtGt);
}

TEST(LexicalConventionLexing, TripleCharLtLtEq) {
  auto r = LexOne("<<=");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLtEq);
}

TEST(LexicalConventionLexing, TripleCharGtGtEq) {
  auto r = LexOne(">>=");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGtEq);
}

TEST(LexicalConventionLexing, TripleCharAmpAmpAmp) {
  auto r = LexOne("&&&");
  EXPECT_EQ(r.token.kind, TokenKind::kAmpAmpAmp);
}

TEST(LexicalConventionLexing, TripleCharPipeDashGt) {
  auto r = LexOne("|->");
  EXPECT_EQ(r.token.kind, TokenKind::kPipeDashGt);
}

TEST(LexicalConventionLexing, TripleCharPipeEqGt) {
  auto r = LexOne("|=>");
  EXPECT_EQ(r.token.kind, TokenKind::kPipeEqGt);
}

TEST(LexicalConventionLexing, TripleCharLtDashGt) {
  auto r = LexOne("<->");
  EXPECT_EQ(r.token.kind, TokenKind::kLtDashGt);
}

TEST(LexicalConventionLexing, TripleCharHashMinusHash) {
  auto r = LexOne("#-#");
  EXPECT_EQ(r.token.kind, TokenKind::kHashMinusHash);
}

TEST(LexicalConventionLexing, TripleCharHashEqHash) {
  auto r = LexOne("#=#");
  EXPECT_EQ(r.token.kind, TokenKind::kHashEqHash);
}

TEST(LexicalConventionLexing, TripleCharDashGtGt) {
  auto r = LexOne("->>");
  EXPECT_EQ(r.token.kind, TokenKind::kDashGtGt);
}

TEST(LexicalConventionLexing, TripleCharPlusSlashMinus) {
  auto r = LexOne("+/-");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusSlashMinus);
}

TEST(LexicalConventionLexing, TripleCharPlusPercentMinus) {
  auto r = LexOne("+%-");
  EXPECT_EQ(r.token.kind, TokenKind::kPlusPercentMinus);
}

TEST(LexicalConventionLexing, QuadCharLtLtLtEq) {
  auto r = LexOne("<<<=");
  EXPECT_EQ(r.token.kind, TokenKind::kLtLtLtEq);
}

TEST(LexicalConventionLexing, QuadCharGtGtGtEq) {
  auto r = LexOne(">>>=");
  EXPECT_EQ(r.token.kind, TokenKind::kGtGtGtEq);
}

TEST(LexicalConventionLexing, OperatorsAdjacentToIdentifiers) {
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

TEST(LexicalConventionLexing, MaximalMunchForOperators) {
  auto tokens = Lex("a===b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, DoubleNotTriple) {
  auto tokens = Lex("a == b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEq);
}

TEST(LexicalConventionLexing, OperatorTokensRecognized) {
  auto tokens = Lex("+ - * / % ** && ||");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPercent);
  EXPECT_EQ(tokens[5].kind, TokenKind::kPower);
  EXPECT_EQ(tokens[6].kind, TokenKind::kAmpAmp);
  EXPECT_EQ(tokens[7].kind, TokenKind::kPipePipe);
}

}  // namespace
