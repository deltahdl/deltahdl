#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "helpers_keyword_table_partition.h"
#include "lexer/keywords.h"
#include "lexer/token.h"
#include "model_keyword_table_sweeps.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

TEST(SystemVerilog2012KeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1800-2012");
  ASSERT_TRUE(parsed.has_value());
  if (!parsed.has_value()) return;
  EXPECT_EQ(*parsed, KeywordVersion::kVer18002012);

  auto previous = ParseKeywordVersion("1800-2009");
  ASSERT_TRUE(previous.has_value());
  if (!previous.has_value()) return;
  EXPECT_NE(*parsed, *previous);

  auto next_standard = ParseKeywordVersion("1800-2017");
  ASSERT_TRUE(next_standard.has_value());
  if (!next_standard.has_value()) return;
  EXPECT_NE(*parsed, *next_standard);
}

TEST(SystemVerilog2012KeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* const kNotThisSpecifier[] = {
      "1800-2012 ", " 1800-2012", "1800_2012", "18002012", "1800-2013",
      "1800-2011",  "1800-12",    "1364-2012", "2012",     "1800-2012-noconfig",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

TEST(SystemVerilog2012KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto under_1995 = LookupKeyword(word, KeywordVersion::kVer13641995);
    ASSERT_TRUE(under_1995.has_value())
        << word << " is one of the words the included list reserves";
    if (!under_1995.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_1995)
        << word << " keeps the same keyword meaning here";
  }
}

TEST(SystemVerilog2012KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywords), 21u);
  for (const char* word : kVerilog2001AddedKeywords) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    ASSERT_TRUE(under_2001.has_value())
        << word << " is one of the words the included list adds";
    if (!under_2001.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_2001)
        << word << " keeps the same keyword meaning here";
  }

  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002012).has_value())
        << word << " is reserved here";
    EXPECT_FALSE(
        LookupKeyword(word, KeywordVersion::kVer13642001Noconfig).has_value())
        << word << " is exactly what the configuration-free list leaves out";
  }
}

TEST(SystemVerilog2012KeywordList, IncludesTheVerilog2005Keyword) {
  ASSERT_EQ(std::size(kVerilog2005AddedKeywords), 1u);
  const char* word = kVerilog2005AddedKeywords[0];

  auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
  ASSERT_TRUE(under_2005.has_value());
  if (!under_2005.has_value()) return;

  auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
  ASSERT_TRUE(here.has_value());
  if (!here.has_value()) return;
  EXPECT_EQ(*here, *under_2005);
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642001).has_value());
}

TEST(SystemVerilog2012KeywordList, IncludesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kSystemVerilog2005AddedKeywords), 97u);
  for (const char* word : kSystemVerilog2005AddedKeywords) {
    auto under_sv2005 = LookupKeyword(word, KeywordVersion::kVer18002005);
    ASSERT_TRUE(under_sv2005.has_value())
        << word << " is one of the words the included list adds";
    if (!under_sv2005.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_sv2005)
        << word << " keeps the same keyword meaning here";

    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642005).has_value())
        << word << " is not reserved by anything that list is built on";
  }
}

TEST(SystemVerilog2012KeywordList, IncludesEverySystemVerilog2009Keyword) {
  EXPECT_EQ(std::size(kSystemVerilog2009AddedKeywords), 23u);
  for (const char* word : kSystemVerilog2009AddedKeywords) {
    auto under_sv2009 = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(under_sv2009.has_value())
        << word << " is one of the words the included list adds";
    if (!under_sv2009.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_sv2009)
        << word << " keeps the same keyword meaning here";

    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002005).has_value())
        << word << " is not reserved by anything that list is built on";
  }
}

TEST(SystemVerilog2012KeywordList,
     AddedWordsAreTheWholeDifferenceFromIncludedLists) {
  EXPECT_EQ(std::size(kSystemVerilog2012AddedKeywords), 4u);

  struct AddedWord {
    const char* text;
    TokenKind kind;
  };
  const AddedWord kAdded[] = {
      {"implements", TokenKind::kKwImplements},
      {"interconnect", TokenKind::kKwInterconnect},
      {"nettype", TokenKind::kKwNettype},
      {"soft", TokenKind::kKwSoft},
  };
  for (const auto& word : kAdded) {
    auto here = LookupKeyword(word.text, KeywordVersion::kVer18002012);
    ASSERT_TRUE(here.has_value())
        << word.text << " is one of the words this version adds";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, word.kind) << word.text;
    EXPECT_FALSE(
        LookupKeyword(word.text, KeywordVersion::kVer18002009).has_value())
        << word.text << " is not reserved by the last of the included lists";
  }

  size_t newly_reserved = 0;
  auto count_new = [&newly_reserved](const char* word) {
    if (!LookupKeyword(word, KeywordVersion::kVer18002009).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer18002012).has_value()) {
      ++newly_reserved;
    }
  };
  for (const char* word : kVerilog1995Keywords) count_new(word);
  for (const char* word : kVerilog2001AddedKeywords) count_new(word);
  for (const char* word : kVerilog2005AddedKeywords) count_new(word);
  for (const char* word : kSystemVerilog2005AddedKeywords) count_new(word);
  for (const char* word : kSystemVerilog2009AddedKeywords) count_new(word);
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

TEST(SystemVerilog2012KeywordList, TheListIsTheSixTablesTogether) {
  ExpectTablesPartitionTheList(
      {kVerilog1995KeywordSweep, kVerilog2001AddedKeywordSweep,
       kVerilog2005AddedKeywordSweep, kSystemVerilog2005AddedKeywordSweep,
       kSystemVerilog2009AddedKeywordSweep,
       kSystemVerilog2012AddedKeywordSweep},
      248);
}

TEST(SystemVerilog2012KeywordList, WordsOutsideTheSixTablesAreNotReserved) {
  const char* const kNotWords[] = {
      "implement",     "implemented",    "implements_",   "interconnects",
      "inter_connect", "interconnected", "nettypes",      "net_type",
      "nettype_",      "softly",         "soft_",         "softer",
      "s_soft",        "endnettype",     "endimplements",
  };
  for (const char* word : kNotWords) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002012).has_value())
        << word << " is not one of the identifiers the six tables list";
  }
}

}  // namespace
