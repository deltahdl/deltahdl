#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

// §22.14.9: the "1800-2017" version_specifier selects the reserved words of
// IEEE Std 1800-2017, which include the identifiers reserved in every prior
// version. Witness one keyword per predecessor era.
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

// §22.14.9: the "1800-2023" version_specifier likewise carries forward the
// reserved words of every prior version.
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

// §22.14.9: "1800-2017" and "1800-2023" do not add any new reserved keywords.
// The newest reserved words originate in IEEE Std 1800-2012 (soft, implements);
// they are already reserved at "1800-2012", so the later specifiers inherit the
// complete set without extending it. Symmetrically, an identifier that is not
// reserved at "1800-2012" stays unreserved at "1800-2017" and "1800-2023" — no
// previously free word is promoted to a keyword.
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
