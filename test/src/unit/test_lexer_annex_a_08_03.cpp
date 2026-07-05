#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ExpressionLexing, IncrementOperator) {
  auto tokens = Lex("++");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusPlus);
}

TEST(ExpressionLexing, DecrementOperator) {
  auto tokens = Lex("--");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kMinusMinus);
}

TEST(ExpressionLexing, ConditionalQuestionAndColon) {
  auto tokens = Lex("a ? b : c");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kQuestion);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
}

TEST(ExpressionLexing, IndexedRangePlusOperator) {
  auto tokens = Lex("a[0+:8]");
  bool found = false;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kPlusColon) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ExpressionLexing, IndexedRangeMinusOperator) {
  auto tokens = Lex("a[7-:8]");
  bool found = false;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kMinusColon) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ExpressionLexing, DollarToken) {
  auto r = LexOne("$");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
}

TEST(ExpressionLexing, ArithmeticBinaryOperators) {
  auto tokens = Lex("+ - * / % **");
  int plus = 0, minus = 0, star = 0, slash = 0, percent = 0, pow = 0;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kPlus) plus++;
    if (t.kind == TokenKind::kMinus) minus++;
    if (t.kind == TokenKind::kStar) star++;
    if (t.kind == TokenKind::kSlash) slash++;
    if (t.kind == TokenKind::kPercent) percent++;
    if (t.kind == TokenKind::kPower) pow++;
  }
  EXPECT_EQ(plus, 1);
  EXPECT_EQ(minus, 1);
  EXPECT_EQ(star, 1);
  EXPECT_EQ(slash, 1);
  EXPECT_EQ(percent, 1);
  EXPECT_EQ(pow, 1);
}

TEST(ExpressionLexing, LogicalAndRelationalOperators) {
  auto tokens = Lex("&& || == != === !== < > <= >=");
  int seen = 0;
  for (const auto& t : tokens) {
    switch (t.kind) {
      case TokenKind::kAmpAmp:
      case TokenKind::kPipePipe:
      case TokenKind::kEqEq:
      case TokenKind::kBangEq:
      case TokenKind::kEqEqEq:
      case TokenKind::kBangEqEq:
      case TokenKind::kLt:
      case TokenKind::kGt:
      case TokenKind::kLtEq:
      case TokenKind::kGtEq:
        seen++;
        break;
      default:
        break;
    }
  }
  EXPECT_EQ(seen, 10);
}

TEST(ExpressionLexing, BitwiseAndShiftOperators) {
  auto tokens = Lex("& | ^ ~^ ~ << >> <<< >>>");
  int seen = 0;
  for (const auto& t : tokens) {
    switch (t.kind) {
      case TokenKind::kAmp:
      case TokenKind::kPipe:
      case TokenKind::kCaret:
      case TokenKind::kCaretTilde:
      case TokenKind::kTildeCaret:
      case TokenKind::kTilde:
      case TokenKind::kLtLt:
      case TokenKind::kGtGt:
      case TokenKind::kLtLtLt:
      case TokenKind::kGtGtGt:
        seen++;
        break;
      default:
        break;
    }
  }
  EXPECT_EQ(seen, 9);
}

TEST(ExpressionLexing, InsideExpressionTokenSequence) {
  auto tokens = Lex("x inside { 1 , 2 }");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwInside);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
}

TEST(ExpressionLexing, TaggedUnionTokenSequence) {
  auto tokens = Lex("tagged Valid 42");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTagged);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
}

TEST(ExpressionLexing, OperatorAssignmentInsideParensTokens) {
  auto tokens = Lex("( y += 1 )");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kPlusEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

TEST(ExpressionLexing, MintypMaxColonSeparatorTokens) {
  auto tokens = Lex("1 : 2 : 3");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIntLiteral);
}

}  // namespace
