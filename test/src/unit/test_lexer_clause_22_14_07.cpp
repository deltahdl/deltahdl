#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2009_NewKeywordsPresent) {
  const char* kNewKeywords[] = {
      "accept_on",      "checker",        "endchecker",   "eventually",
      "global",         "implies",        "let",          "nexttime",
      "reject_on",      "restrict",       "s_always",     "s_eventually",
      "s_nexttime",     "s_until",        "s_until_with", "strong",
      "sync_accept_on", "sync_reject_on", "unique0",      "until",
      "until_with",     "untyped",        "weak",
  };
  for (const char* kw : kNewKeywords) {
    auto result = LookupKeyword(kw, KeywordVersion::kVer18002009);
    EXPECT_TRUE(result.has_value())
        << kw << " should be a keyword in 1800-2009";
  }
}

TEST(Lexer, KeywordVersion_1800_2009_NewKeywordsNotIn1800_2005) {
  const char* kNewKeywords[] = {
      "accept_on", "checker", "endchecker", "eventually", "global",
      "implies",   "let",     "nexttime",   "reject_on",  "restrict",
  };
  for (const char* kw : kNewKeywords) {
    auto result = LookupKeyword(kw, KeywordVersion::kVer18002005);
    EXPECT_FALSE(result.has_value())
        << kw << " should NOT be a keyword in 1800-2005";
  }
}

TEST(Lexer, KeywordVersion_1800_2009_Includes1800_2005Keywords) {
  EXPECT_TRUE(LookupKeyword("logic", KeywordVersion::kVer18002009).has_value());
  EXPECT_TRUE(
      LookupKeyword("interface", KeywordVersion::kVer18002009).has_value());
  EXPECT_TRUE(LookupKeyword("class", KeywordVersion::kVer18002009).has_value());
  EXPECT_TRUE(LookupKeyword("enum", KeywordVersion::kVer18002009).has_value());
}

TEST(Lexer, KeywordVersion_1800_2009_ImplementsNotKeyword) {
  auto kw = LookupKeyword("implements", KeywordVersion::kVer18002009);
  EXPECT_FALSE(kw.has_value());
}

}
