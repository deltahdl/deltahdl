#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockLexing, AllSixUnitsLexAsTimeLiteral) {
  EXPECT_EQ(LexOne("1s").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1ms").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1us").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1ns").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1ps").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1fs").token.kind, TokenKind::kTimeLiteral);
}

// §5.8 lists s, ms, us, ns, ps and fs as the time units, so the x of `1xs` is
// not one of them and Lexer::TryLexTimeSuffix consumes nothing. This fails if
// `1xs` lexes as one token, or as a time literal, instead of the integer
// literal `1` followed by the identifier `xs`.
TEST(DesignBuildingBlockLexing, SuffixXsLexesAsIntLiteralThenIdentifier) {
  auto tokens = Lex("1xs");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "xs");
}

// §5.8 gives s as a time unit on its own, and the e of `1sec` follows it, so
// Lexer::IsWordBoundary refuses the suffix and Lexer::TryLexTimeSuffix puts
// pos_ back. This fails if the s is taken as a unit, which would lex `1s`
// followed by the identifier `ec`, or if `1sec` lexes as a time literal.
TEST(DesignBuildingBlockLexing, SuffixSecLexesAsIntLiteralThenIdentifier) {
  auto tokens = Lex("1sec");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "sec");
}

// §5.6 rules that identifiers are case sensitive, so the NS of `1NS` is not
// the ns §5.8 lists and Lexer::TryLexTimeSuffix, which compares against the
// lower-case letters only, consumes nothing. This fails if the comparison is
// made case-insensitively, which would lex `1NS` as one time literal.
TEST(DesignBuildingBlockLexing, UpperCaseNsLexesAsIntLiteralThenIdentifier) {
  auto tokens = Lex("1NS");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "NS");
}

TEST(DesignBuildingBlockLexing, RangeBoundsAcceptedByLexer) {
  EXPECT_EQ(LexOne("100s").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1fs").token.kind, TokenKind::kTimeLiteral);
}

TEST(DesignBuildingBlockLexing, NumberAloneIsIntLiteralNotTimeLiteral) {
  EXPECT_EQ(LexOne("1").token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(LexOne("100").token.kind, TokenKind::kIntLiteral);
}

}  // namespace
