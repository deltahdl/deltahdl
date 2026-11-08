#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "lexer/keywords.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

constexpr const char* kExcluded[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

constexpr const char* kKept[] = {
    "automatic",
    "endgenerate",
    "generate",
    "genvar",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
};

bool IsExcluded(const std::string& word) {
  for (const char* w : kExcluded) {
    if (word == w) return true;
  }
  return false;
}

TEST(NoconfigKeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1364-2001-noconfig");
  ASSERT_TRUE(parsed.has_value());
  if (!parsed.has_value()) return;
  EXPECT_EQ(*parsed, KeywordVersion::kVer13642001Noconfig);

  auto plain = ParseKeywordVersion("1364-2001");
  ASSERT_TRUE(plain.has_value());
  if (!plain.has_value()) return;
  EXPECT_NE(*parsed, *plain);
}

TEST(NoconfigKeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* const kNotThisSpecifier[] = {
      "1364-2001-NOCONFIG",  "1364-2001-Noconfig",
      "1364-2001noconfig",   "1364-2001 -noconfig",
      "1364-2001-noconfig ", " 1364-2001-noconfig",
      "1364-2001-no-config", "noconfig",
      "1364-2001-noconfigx",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

TEST(NoconfigKeywordList, MatchesVerilog2001ExceptForTheExcludedTen) {
  size_t excluded_seen = 0;
  size_t kept_seen = 0;

  auto compare = [&](const char* word) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    auto under_noconfig =
        LookupKeyword(word, KeywordVersion::kVer13642001Noconfig);

    ASSERT_TRUE(under_2001.has_value())
        << word << " is reserved by the version this one is defined from";

    if (IsExcluded(word)) {
      EXPECT_FALSE(under_noconfig.has_value())
          << word << " is one of the ten this version drops";
      ++excluded_seen;
    } else {
      ASSERT_TRUE(under_noconfig.has_value())
          << word << " is not among the ten and stays reserved";
      EXPECT_EQ(*under_noconfig, *under_2001)
          << word << " keeps the same keyword meaning under both versions";
      ++kept_seen;
    }
  };

  for (const char* word : kVerilog1995Keywords) compare(word);
  for (const char* word : kExcluded) compare(word);
  for (const char* word : kKept) compare(word);

  EXPECT_EQ(excluded_seen, 10u);
  EXPECT_EQ(kept_seen, std::size(kVerilog1995Keywords) + std::size(kKept));
}

TEST(NoconfigKeywordList, SplitsVerilog2001AdditionsIntoTenAndEleven) {
  EXPECT_EQ(std::size(kExcluded), 10u);
  EXPECT_EQ(std::size(kKept), 11u);
  EXPECT_EQ(std::size(kExcluded) + std::size(kKept), 21u);
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);

  for (const char* word : kKept) {
    EXPECT_FALSE(IsExcluded(word)) << word;
  }
}

TEST(NoconfigKeywordList, KeepsAllVerilog1995Keywords) {
  for (const char* kw : kVerilog1995Keywords) {
    EXPECT_TRUE(
        LookupKeyword(kw, KeywordVersion::kVer13642001Noconfig).has_value())
        << kw << " is inherited from Table 22-1 and stays reserved";
  }
}

TEST(NoconfigKeywordList, LaterVersionKeywordsAreNotRecognized) {
  const char* const kLater[] = {
      "uwire",   "logic",       "interface", "bit",        "byte",
      "int",     "always_comb", "package",   "endpackage", "shortreal",
      "nettype", "soft",        "untyped",
  };
  for (const char* kw : kLater) {
    EXPECT_FALSE(
        LookupKeyword(kw, KeywordVersion::kVer13642001Noconfig).has_value())
        << kw << " belongs to a later list than this one";
  }
}

}  // namespace
