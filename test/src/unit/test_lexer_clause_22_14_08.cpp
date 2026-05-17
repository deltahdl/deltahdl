#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2012_NewKeywordsPresent) {
  EXPECT_EQ(LookupKeyword("implements", KeywordVersion::kVer18002012),
            std::optional(TokenKind::kKwImplements));
  EXPECT_EQ(LookupKeyword("interconnect", KeywordVersion::kVer18002012),
            std::optional(TokenKind::kKwInterconnect));
  EXPECT_EQ(LookupKeyword("nettype", KeywordVersion::kVer18002012),
            std::optional(TokenKind::kKwNettype));
  EXPECT_EQ(LookupKeyword("soft", KeywordVersion::kVer18002012),
            std::optional(TokenKind::kKwSoft));
}

TEST(Lexer, KeywordVersion_1800_2012_NewKeywordsNotIn1800_2009) {
  EXPECT_FALSE(
      LookupKeyword("implements", KeywordVersion::kVer18002009).has_value());
  EXPECT_FALSE(
      LookupKeyword("interconnect", KeywordVersion::kVer18002009).has_value());
  EXPECT_FALSE(
      LookupKeyword("nettype", KeywordVersion::kVer18002009).has_value());
  EXPECT_FALSE(LookupKeyword("soft", KeywordVersion::kVer18002009).has_value());
}

TEST(Lexer, KeywordVersion_1800_2012_IncludesAllPriorVersions) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002012).has_value());
  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer18002012).has_value());
  EXPECT_TRUE(LookupKeyword("uwire", KeywordVersion::kVer18002012).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002012).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002012).has_value());
}

}
