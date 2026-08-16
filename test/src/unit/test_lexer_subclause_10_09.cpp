#include "fixture_lexer.h"
#include "helpers_assignment_pattern_lex.h"

using namespace delta;

namespace {

TEST(AssignmentPatternLex, ApostropheBraceDistinctFromConcatBrace) {
  auto plain = Lex("{1, 2}");
  ASSERT_GE(plain.size(), 1u);
  EXPECT_NE(plain[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(plain[0].kind, TokenKind::kLBrace);

  auto pat = Lex("'{1, 2}");
  ASSERT_GE(pat.size(), 1u);
  EXPECT_EQ(pat[0].kind, TokenKind::kApostropheLBrace);
}

TEST(AssignmentPatternLex, DefaultKeyword) {
  auto tokens = Lex("'{default: 0}");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwDefault);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
}

TEST(AssignmentPatternLex, SimpleTypeKeywordAsKey) {
  auto tokens = Lex("'{int: 5, default: 0}");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwInt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwDefault);
}

TEST(AssignmentPatternLex, IntegerAtomTypePrefixTokenization) {
  auto tokens = Lex("int'{42}");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRBrace);
}

TEST(AssignmentPatternLex, PsTypeIdentifierPrefixTokenization) {
  auto tokens = Lex("my_t'{1, 2}");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}

TEST(AssignmentPatternLex, ConstantExpressionReplicationPrefix) {
  ExpectReplicationPatternTokens("'{4{8'hAB}}");
}

TEST(AssignmentPatternLex, EmptyAssignmentPatternTokens) {
  auto tokens = Lex("'{}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kRBrace);
}

// Lexing "' {1, 2}" yields TokenKind::kApostropheLBrace as its first token.
// A.6.7.1 writes assignment_pattern ::= ' { expression { , expression } }, so
// the apostrophe and the { are two separate grammar terminals. §5.3 rules that
// white space "shall be ignored except when they serve to separate other
// lexical tokens", so a space standing between those two terminals is legal.
// The two terminals still lex as one TokenKind::kApostropheLBrace token, which
// AssignmentPatternLex.ApostropheBraceDistinctFromConcatBrace above keeps
// distinct from TokenKind::kLBrace.
TEST(AssignmentPatternLex,
     WhiteSpaceBetweenApostropheAndLBraceLexesApostropheLBrace) {
  auto tokens = Lex("' {1, 2}");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
}

}  // namespace
