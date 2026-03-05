#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// §22.14.9 — IEEE Std 1800-2017 and IEEE Std 1800-2023 add no new keywords.

TEST(Lexer, KeywordVersion_1800_2017_SameAs1800_2012) {
  // Verify that 1800-2017 recognizes all 1800-2012 keywords (spot-check).
  EXPECT_TRUE(LookupKeyword("implements", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("interconnect", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("nettype", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002017).has_value());
  EXPECT_TRUE(LookupKeyword("checker", KeywordVersion::kVer18002017).has_value());
}

TEST(Lexer, KeywordVersion_1800_2023_SameAs1800_2017) {
  // Verify that 1800-2023 recognizes all 1800-2017 keywords (spot-check).
  EXPECT_TRUE(LookupKeyword("implements", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("interconnect", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("nettype", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("soft", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("checker", KeywordVersion::kVer18002023).has_value());
  EXPECT_TRUE(LookupKeyword("module", KeywordVersion::kVer18002023).has_value());
}

TEST(Lexer, KeywordVersion_1800_2017_And_2023_NoNewKeywords) {
  // The keyword map has no entries with min_version > 1800-2012.
  // Verify a non-keyword stays non-keyword.
  EXPECT_FALSE(LookupKeyword("foobar", KeywordVersion::kVer18002017).has_value());
  EXPECT_FALSE(LookupKeyword("foobar", KeywordVersion::kVer18002023).has_value());
}

}  // namespace
