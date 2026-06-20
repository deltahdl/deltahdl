#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1364_2001_AllAdditionalKeywordsRecognized) {
  const char* table22_dot2[] = {
      "automatic",
      "cell",
      "config",
      "design",
      "endconfig",
      "endgenerate",
      "generate",
      "genvar",
      "incdir",
      "include",
      "instance",
      "liblist",
      "library",
      "localparam",
      "noshowcancelled",
      "pulsestyle_ondetect",
      "pulsestyle_onevent",
      "showcancelled",
      "signed",
      "unsigned",
      "use",
  };
  for (const char* kw : table22_dot2) {
    auto result = LookupKeyword(kw, KeywordVersion::kVer13642001);
    EXPECT_TRUE(result.has_value())
        << kw << " should be a keyword in 1364-2001";
  }
}

TEST(Lexer, KeywordVersion_1364_2001_Includes1364_1995Keywords) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer13642001).has_value());
  EXPECT_TRUE(LookupKeyword("wire", KeywordVersion::kVer13642001).has_value());
  EXPECT_TRUE(LookupKeyword("reg", KeywordVersion::kVer13642001).has_value());
  EXPECT_TRUE(
      LookupKeyword("always", KeywordVersion::kVer13642001).has_value());
  EXPECT_TRUE(
      LookupKeyword("initial", KeywordVersion::kVer13642001).has_value());
}

TEST(Lexer, KeywordVersion_1364_2001_LaterKeywordsNotRecognized) {
  EXPECT_FALSE(
      LookupKeyword("uwire", KeywordVersion::kVer13642001).has_value());

  EXPECT_FALSE(
      LookupKeyword("logic", KeywordVersion::kVer13642001).has_value());
  EXPECT_FALSE(LookupKeyword("bit", KeywordVersion::kVer13642001).has_value());
  EXPECT_FALSE(
      LookupKeyword("interface", KeywordVersion::kVer13642001).has_value());
  EXPECT_FALSE(
      LookupKeyword("class", KeywordVersion::kVer13642001).has_value());

  EXPECT_FALSE(
      LookupKeyword("checker", KeywordVersion::kVer13642001).has_value());
}

TEST(Lexer, KeywordVersion_1364_2001_NonKeywordIdentifier) {
  auto kw = LookupKeyword("my_signal", KeywordVersion::kVer13642001);
  EXPECT_FALSE(kw.has_value());
}

}  // namespace
