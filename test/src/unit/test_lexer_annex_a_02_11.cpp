#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- Covergroup declaration keywords ---

TEST(CovergroupKeywordLexing, CovergroupKeyword) {
  auto r = LexOne("covergroup");
  EXPECT_EQ(r.token.kind, TokenKind::kKwCovergroup);
  EXPECT_EQ(r.token.text, "covergroup");
}

TEST(CovergroupKeywordLexing, EndgroupKeyword) {
  auto r = LexOne("endgroup");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndgroup);
  EXPECT_EQ(r.token.text, "endgroup");
}

TEST(CovergroupKeywordLexing, CoverpointKeyword) {
  auto r = LexOne("coverpoint");
  EXPECT_EQ(r.token.kind, TokenKind::kKwCoverpoint);
  EXPECT_EQ(r.token.text, "coverpoint");
}

TEST(CovergroupKeywordLexing, CrossKeyword) {
  auto r = LexOne("cross");
  EXPECT_EQ(r.token.kind, TokenKind::kKwCross);
  EXPECT_EQ(r.token.text, "cross");
}

TEST(CovergroupKeywordLexing, BinsKeyword) {
  auto r = LexOne("bins");
  EXPECT_EQ(r.token.kind, TokenKind::kKwBins);
  EXPECT_EQ(r.token.text, "bins");
}

TEST(CovergroupKeywordLexing, IllegalBinsKeyword) {
  auto r = LexOne("illegal_bins");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIllegalBins);
  EXPECT_EQ(r.token.text, "illegal_bins");
}

TEST(CovergroupKeywordLexing, IgnoreBinsKeyword) {
  auto r = LexOne("ignore_bins");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIgnoreBins);
  EXPECT_EQ(r.token.text, "ignore_bins");
}

TEST(CovergroupKeywordLexing, BinsofKeyword) {
  auto r = LexOne("binsof");
  EXPECT_EQ(r.token.kind, TokenKind::kKwBinsof);
  EXPECT_EQ(r.token.text, "binsof");
}

TEST(CovergroupKeywordLexing, WildcardKeyword) {
  auto r = LexOne("wildcard");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWildcard);
  EXPECT_EQ(r.token.text, "wildcard");
}

TEST(CovergroupKeywordLexing, IntersectKeyword) {
  auto r = LexOne("intersect");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIntersect);
  EXPECT_EQ(r.token.text, "intersect");
}

// --- Block event operator ---

TEST(CovergroupOperatorLexing, DoubleAtOperator) {
  auto tokens = Lex("@@(begin phase)");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAtAt);
  EXPECT_EQ(tokens[0].text, "@@");
}

TEST(CovergroupOperatorLexing, DoubleAtWithSpace) {
  auto tokens = Lex("@@ (begin phase)");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAtAt);
  EXPECT_EQ(tokens[0].text, "@@");
}

TEST(CovergroupOperatorLexing, DoubleAtInContext) {
  auto tokens = Lex("covergroup cg @@(begin task1)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwCovergroup);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAtAt);
}

// --- Keyword not confused with identifier ---

TEST(CovergroupKeywordLexing, CovergroupNotIdentifier) {
  auto tokens = Lex("covergroup cg");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwCovergroup);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(CovergroupKeywordLexing, BinsNotIdentifier) {
  auto tokens = Lex("bins a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBins);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(CovergroupKeywordLexing, BinsofNotIdentifier) {
  auto tokens = Lex("binsof(cp1)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBinsof);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
}

// --- Option and type_option are identifiers ---

TEST(CovergroupKeywordLexing, OptionIsIdentifier) {
  auto r = LexOne("option");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "option");
}

TEST(CovergroupKeywordLexing, TypeOptionIsIdentifier) {
  auto tokens = Lex("type_option");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "type_option");
}

}  // namespace
