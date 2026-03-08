#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1364_2005_UwireIsKeyword) {
  auto kw = LookupKeyword("uwire", KeywordVersion::kVer13642005);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwUwire));
}

TEST(Lexer, KeywordVersion_1364_2005_UwireNotIn1364_2001) {
  auto kw = LookupKeyword("uwire", KeywordVersion::kVer13642001);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersion_1364_2005_LogicIsNotKeyword) {
  auto kw = LookupKeyword("logic", KeywordVersion::kVer13642005);
  EXPECT_FALSE(kw.has_value());
}

TEST(Lexer, KeywordVersion_1364_2005_Includes1364_2001Keywords) {

  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer13642005).has_value());
  EXPECT_TRUE(
      LookupKeyword("generate", KeywordVersion::kVer13642005).has_value());
  EXPECT_TRUE(
      LookupKeyword("localparam", KeywordVersion::kVer13642005).has_value());
  EXPECT_TRUE(
      LookupKeyword("signed", KeywordVersion::kVer13642005).has_value());
  EXPECT_TRUE(
      LookupKeyword("unsigned", KeywordVersion::kVer13642005).has_value());
}

TEST(Lexer, KeywordVersion_1364_2005_Includes1364_1995Keywords) {

  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer13642005).has_value());
  EXPECT_TRUE(LookupKeyword("wire", KeywordVersion::kVer13642005).has_value());
  EXPECT_TRUE(LookupKeyword("reg", KeywordVersion::kVer13642005).has_value());
}

TEST(Lexer, KeywordVersion_1364_2005_InterfaceIsNotKeyword) {

  auto kw = LookupKeyword("interface", KeywordVersion::kVer13642005);
  EXPECT_FALSE(kw.has_value());
}

}
