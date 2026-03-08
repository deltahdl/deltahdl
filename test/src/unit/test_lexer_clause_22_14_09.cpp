#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2017_SameAs1800_2012) {

  EXPECT_TRUE(
      LookupKeyword("implements", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("interconnect", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("nettype", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002017).has_value());
}

TEST(Lexer, KeywordVersion_1800_2023_SameAs1800_2017) {

  EXPECT_TRUE(
      LookupKeyword("implements", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("interconnect", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("nettype", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002023).has_value());
}

TEST(Lexer, KeywordVersion_1800_2017_And_2023_NoNewKeywords) {

  EXPECT_FALSE(
      LookupKeyword("foobar", KeywordVersion::kVer18002017).has_value());
  EXPECT_FALSE(
      LookupKeyword("foobar", KeywordVersion::kVer18002023).has_value());
}

}
