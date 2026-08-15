#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "lexer/token.h"

namespace delta {
namespace {

// No subclause of IEEE 1800-2023 says what a tool calls a token it reports on,
// so these cases cover TokenKindName on its own terms. What they hold it to is
// that the name identifies the token: a keyword answers the word the source
// wrote and punctuation answers the characters, both quoted, so that the "got
// ..." half of a parser report names something the reader can find in their own
// source. A kind with no spelling of its own makes every report of it read the
// same as a report of any other kind, which is what a reader loses.

// Every kind answers something, swept over the enum from its first enumerator
// to kLastTokenKind rather than over a list of kinds written out here. A list
// would be a second inventory of TokenKind: a kind added to the enum after it
// would answer nothing with no case going red. "token" is the answer the 261
// unspelled kinds shared, and "unnamed token kind" is what the default arm of
// TokenKindName answers, so a kind giving either is a kind nothing spells.
TEST(TokenKindName, EveryKindHasASpelling) {
  for (auto raw = static_cast<unsigned>(TokenKind::kEof);
       raw <= static_cast<unsigned>(TokenKind::kLastTokenKind); ++raw) {
    auto kind = static_cast<TokenKind>(static_cast<uint16_t>(raw));
    std::string_view name = TokenKindName(kind);
    EXPECT_FALSE(name.empty()) << "TokenKind " << raw << " answers nothing";
    EXPECT_NE(name, std::string_view("token"))
        << "TokenKind " << raw << " answers the name every kind would answer";
    EXPECT_NE(name, std::string_view("unnamed token kind"))
        << "TokenKind " << raw << " reaches the default arm of TokenKindName";
  }
}

// A keyword answers the spelling the keyword table in src/lexer/keywords.cpp
// maps to it, quoted. The six are drawn from six of the versions that table
// records a keyword against -- 1364-1995, 1364-2001, 1364-2005, 1800-2005,
// 1800-2009 and 1800-2012 -- rather than from one run of adjacent entries, so
// a name derived from part of the table only is a name six words apart cannot
// all keep.
TEST(TokenKindName, KeywordsAreSpelledAsWritten) {
  EXPECT_EQ(TokenKindName(TokenKind::kKwModule), "'module'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwAutomatic), "'automatic'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwUwire), "'uwire'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwLogic), "'logic'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwNexttime), "'nexttime'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwNettype), "'nettype'");
}

// The thirteen punctuation kinds that are not operators of §11.3 Table 11-1,
// each asserted by name. The sweep above says that each answers something; this
// says which characters each answers, which is what tells a report of a '@'
// from a report of a '@@'.
TEST(TokenKindName, PunctuationIsSpelledAsWritten) {
  EXPECT_EQ(TokenKindName(TokenKind::kAmpAmpAmp), "'&&&'");
  EXPECT_EQ(TokenKindName(TokenKind::kAt), "'@'");
  EXPECT_EQ(TokenKindName(TokenKind::kAtAt), "'@@'");
  EXPECT_EQ(TokenKindName(TokenKind::kColonColon), "'::'");
  EXPECT_EQ(TokenKindName(TokenKind::kDashGtGt), "'->>'");
  EXPECT_EQ(TokenKindName(TokenKind::kDollar), "'$'");
  EXPECT_EQ(TokenKindName(TokenKind::kDotStar), "'.*'");
  EXPECT_EQ(TokenKindName(TokenKind::kEqGt), "'=>'");
  EXPECT_EQ(TokenKindName(TokenKind::kMinusColon), "'-:'");
  EXPECT_EQ(TokenKindName(TokenKind::kPipeDashGt), "'|->'");
  EXPECT_EQ(TokenKindName(TokenKind::kPipeEqGt), "'|=>'");
  EXPECT_EQ(TokenKindName(TokenKind::kPlusColon), "'+:'");
  EXPECT_EQ(TokenKindName(TokenKind::kStarGt), "'*>'");
}

}  // namespace
}  // namespace delta
