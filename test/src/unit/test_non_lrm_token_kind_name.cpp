#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <string_view>

#include "lexer/token.h"

namespace delta {
namespace {

TEST(TokenKindName, EveryKindHasASpellingOfItsOwn) {
  std::map<std::string_view, unsigned> first_kind_named;
  for (auto raw = static_cast<unsigned>(TokenKind::kEof);
       raw <= static_cast<unsigned>(TokenKind::kLastTokenKind); ++raw) {
    auto kind = static_cast<TokenKind>(static_cast<uint16_t>(raw));
    std::string_view name = TokenKindName(kind);
    EXPECT_FALSE(name.empty()) << "TokenKind " << raw << " answers nothing";
    EXPECT_NE(name, std::string_view("token"))
        << "TokenKind " << raw << " answers the name every kind would answer";
    auto [it, fresh] = first_kind_named.emplace(name, raw);
    EXPECT_TRUE(fresh) << "TokenKind " << raw << " answers " << name
                       << ", as TokenKind " << it->second << " does";
  }
}

TEST(TokenKindName, KeywordsAreSpelledAsWritten) {
  EXPECT_EQ(TokenKindName(TokenKind::kKwModule), "'module'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwAutomatic), "'automatic'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwUwire), "'uwire'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwLogic), "'logic'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwNexttime), "'nexttime'");
  EXPECT_EQ(TokenKindName(TokenKind::kKwNettype), "'nettype'");
}

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
