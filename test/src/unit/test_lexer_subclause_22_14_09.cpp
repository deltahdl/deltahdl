#include <gtest/gtest.h>

#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2017_IncludesAllPriorVersions) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("uwire", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002017).has_value());
}

TEST(Lexer, KeywordVersion_1800_2023_IncludesAllPriorVersions) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("automatic", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("uwire", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(
      LookupKeyword("checker", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002023).has_value());
}

TEST(Lexer, KeywordVersion_1800_2017_And_2023_AddNoNewKeywords) {
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002012).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002023).has_value());

  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer18002012).has_value());
  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer18002017).has_value());
  EXPECT_FALSE(
      LookupKeyword("my_signal", KeywordVersion::kVer18002023).has_value());
}

}  // namespace
