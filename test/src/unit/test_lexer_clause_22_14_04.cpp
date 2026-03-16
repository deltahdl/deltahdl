#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_Noconfig_ExcludesConfigKeywords) {
  auto kw = LookupKeyword("config", KeywordVersion::kVer13642001Noconfig);
  EXPECT_FALSE(kw.has_value());

  auto gen = LookupKeyword("generate", KeywordVersion::kVer13642001Noconfig);
  EXPECT_TRUE(gen.has_value());
}

TEST(Lexer, KeywordVersion_Noconfig_AllExcludedKeywordsRejected) {
  const char* kExcluded[] = {
      "cell",    "config",   "design",  "endconfig", "incdir",
      "include", "instance", "liblist", "library",   "use",
  };
  for (const char* kw : kExcluded) {
    auto result =
        LookupKeyword(kw, KeywordVersion::kVer13642001Noconfig);
    EXPECT_FALSE(result.has_value())
        << kw << " should be excluded in 1364-2001-noconfig";
  }
}

TEST(Lexer, KeywordVersion_Noconfig_NonExcluded2001KeywordsRecognized) {
  const char* kKept[] = {
      "automatic",          "endgenerate",
      "generate",           "genvar",
      "localparam",         "noshowcancelled",
      "pulsestyle_ondetect", "pulsestyle_onevent",
      "showcancelled",      "signed",
      "unsigned",
  };
  for (const char* kw : kKept) {
    auto result =
        LookupKeyword(kw, KeywordVersion::kVer13642001Noconfig);
    EXPECT_TRUE(result.has_value())
        << kw << " should be a keyword in 1364-2001-noconfig";
  }
}

TEST(Lexer, KeywordVersion_Noconfig_Includes1364_1995Keywords) {
  EXPECT_TRUE(
      LookupKeyword("module", KeywordVersion::kVer13642001Noconfig)
          .has_value());
  EXPECT_TRUE(
      LookupKeyword("wire", KeywordVersion::kVer13642001Noconfig)
          .has_value());
  EXPECT_TRUE(
      LookupKeyword("reg", KeywordVersion::kVer13642001Noconfig)
          .has_value());
  EXPECT_TRUE(
      LookupKeyword("always", KeywordVersion::kVer13642001Noconfig)
          .has_value());
}

TEST(Lexer, KeywordVersion_Noconfig_LaterKeywordsNotRecognized) {
  EXPECT_FALSE(
      LookupKeyword("uwire", KeywordVersion::kVer13642001Noconfig)
          .has_value());
  EXPECT_FALSE(
      LookupKeyword("logic", KeywordVersion::kVer13642001Noconfig)
          .has_value());
  EXPECT_FALSE(
      LookupKeyword("interface", KeywordVersion::kVer13642001Noconfig)
          .has_value());
}

TEST(Lexer, KeywordVersion_Noconfig_ExcludedKeywordsStillInRegular2001) {
  const char* kExcluded[] = {
      "cell",    "config",   "design",  "endconfig", "incdir",
      "include", "instance", "liblist", "library",   "use",
  };
  for (const char* kw : kExcluded) {
    auto result = LookupKeyword(kw, KeywordVersion::kVer13642001);
    EXPECT_TRUE(result.has_value())
        << kw << " should still be a keyword in regular 1364-2001";
  }
}

}  // namespace
