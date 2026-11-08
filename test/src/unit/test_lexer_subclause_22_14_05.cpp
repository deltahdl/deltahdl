#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "lexer/keywords.h"
#include "lexer/token.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

TEST(Verilog2005KeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1364-2005");
  ASSERT_TRUE(parsed.has_value());
  if (!parsed.has_value()) return;
  EXPECT_EQ(*parsed, KeywordVersion::kVer13642005);

  auto extended = ParseKeywordVersion("1364-2001");
  ASSERT_TRUE(extended.has_value());
  if (!extended.has_value()) return;
  EXPECT_NE(*parsed, *extended);

  auto same_year = ParseKeywordVersion("1800-2005");
  ASSERT_TRUE(same_year.has_value());
  if (!same_year.has_value()) return;
  EXPECT_NE(*parsed, *same_year);
}

TEST(Verilog2005KeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* const kNotThisSpecifier[] = {
      "1364-2005 ", " 1364-2005", "1364_2005", "13642005", "1364-2006",
      "1364-2004",  "1364-05",    "2005",      "1364",     "1364-2005-noconfig",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

TEST(Verilog2005KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto under_1995 = LookupKeyword(word, KeywordVersion::kVer13641995);
    ASSERT_TRUE(under_1995.has_value())
        << word << " is one of the words the included list reserves";
    if (!under_1995.has_value()) continue;

    auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
    ASSERT_TRUE(under_2005.has_value())
        << word << " is included by this version";
    if (!under_2005.has_value()) continue;
    EXPECT_EQ(*under_2005, *under_1995)
        << word << " keeps the same keyword meaning here";
  }
}

TEST(Verilog2005KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywords), 21u);
  for (const char* word : kVerilog2001AddedKeywords) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    ASSERT_TRUE(under_2001.has_value())
        << word << " is one of the words the included list adds";
    if (!under_2001.has_value()) continue;

    auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
    ASSERT_TRUE(under_2005.has_value())
        << word << " is included by this version";
    if (!under_2005.has_value()) continue;
    EXPECT_EQ(*under_2005, *under_2001)
        << word << " keeps the same keyword meaning here";
  }
}

TEST(Verilog2005KeywordList, AddsExactlyOneWordOfItsOwn) {
  ASSERT_EQ(std::size(kVerilog2005AddedKeywords), 1u);
  const char* added = kVerilog2005AddedKeywords[0];

  auto here = LookupKeyword(added, KeywordVersion::kVer13642005);
  ASSERT_TRUE(here.has_value());
  if (!here.has_value()) return;
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(added, KeywordVersion::kVer13641995).has_value())
      << added << " is not reserved by the earlier of the two included lists";
  EXPECT_FALSE(LookupKeyword(added, KeywordVersion::kVer13642001).has_value())
      << added << " is not reserved by the later of the two included lists";

  size_t newly_reserved = 0;
  for (const char* word : kVerilog1995Keywords) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642001).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer13642005).has_value()) {
      ++newly_reserved;
    }
  }
  for (const char* word : kVerilog2001AddedKeywords) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642001).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer13642005).has_value()) {
      ++newly_reserved;
    }
  }
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

TEST(Verilog2005KeywordList, TheListIsTheThreeTablesTogether) {
  EXPECT_EQ(std::size(kVerilog1995Keywords) +
                std::size(kVerilog2001AddedKeywords) +
                std::size(kVerilog2005AddedKeywords),
            124u);

  auto in_verilog1995_keywords = [](const std::string& word) {
    for (const char* w : kVerilog1995Keywords) {
      if (word == w) return true;
    }
    return false;
  };
  for (const char* word : kVerilog2001AddedKeywords) {
    EXPECT_FALSE(in_verilog1995_keywords(word)) << word << " is counted twice";
  }
  for (const char* word : kVerilog2005AddedKeywords) {
    EXPECT_FALSE(in_verilog1995_keywords(word)) << word << " is counted twice";
    for (const char* w : kVerilog2001AddedKeywords) {
      EXPECT_NE(std::string(word), w) << word << " is counted twice";
    }
  }
}

TEST(Verilog2005KeywordList, WordsOutsideTheThreeTablesAreNotReserved) {
  const char* const kLater[] = {
      "logic",     "interface", "endinterface", "bit",       "byte",
      "int",       "shortint",  "longint",      "shortreal", "always_comb",
      "always_ff", "package",   "endpackage",   "program",   "class",
      "endclass",  "typedef",   "enum",         "struct",    "union",
      "string",    "void",      "return",       "break",     "unique",
      "nettype",   "soft",      "untyped",      "checker",   "let",
      "global",    "assert",    "cover",        "final",     "var",
  };
  for (const char* word : kLater) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642005).has_value())
        << word << " belongs to a list later than the three this one names";
  }
}

}  // namespace
