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

TEST(SystemVerilog2009KeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1800-2009");
  ASSERT_TRUE(parsed.has_value());
  if (!parsed.has_value()) return;
  EXPECT_EQ(*parsed, KeywordVersion::kVer18002009);

  auto previous = ParseKeywordVersion("1800-2005");
  ASSERT_TRUE(previous.has_value());
  if (!previous.has_value()) return;
  EXPECT_NE(*parsed, *previous);

  auto next_standard = ParseKeywordVersion("1800-2012");
  ASSERT_TRUE(next_standard.has_value());
  if (!next_standard.has_value()) return;
  EXPECT_NE(*parsed, *next_standard);
}

TEST(SystemVerilog2009KeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* const kNotThisSpecifier[] = {
      "1800-2009 ", " 1800-2009", "1800_2009", "18002009", "1800-2010",
      "1800-2008",  "1800-09",    "1364-2009", "2009",     "1800-2009-noconfig",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

TEST(SystemVerilog2009KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto under_1995 = LookupKeyword(word, KeywordVersion::kVer13641995);
    ASSERT_TRUE(under_1995.has_value())
        << word << " is one of the words the included list reserves";
    if (!under_1995.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_1995)
        << word << " keeps the same keyword meaning here";
  }
}

TEST(SystemVerilog2009KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywords), 21u);
  for (const char* word : kVerilog2001AddedKeywords) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    ASSERT_TRUE(under_2001.has_value())
        << word << " is one of the words the included list adds";
    if (!under_2001.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_2001)
        << word << " keeps the same keyword meaning here";
  }

  EXPECT_EQ(std::size(kConfigurationWords), 10u);
  for (const char* word : kConfigurationWords) {
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002009).has_value())
        << word << " is reserved here";
    EXPECT_FALSE(
        LookupKeyword(word, KeywordVersion::kVer13642001Noconfig).has_value())
        << word << " is exactly what the configuration-free list leaves out";
  }
}

TEST(SystemVerilog2009KeywordList, IncludesTheVerilog2005Keyword) {
  ASSERT_EQ(std::size(kVerilog2005AddedKeywords), 1u);
  const char* word = kVerilog2005AddedKeywords[0];

  auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
  ASSERT_TRUE(under_2005.has_value());
  if (!under_2005.has_value()) return;

  auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
  ASSERT_TRUE(here.has_value());
  if (!here.has_value()) return;
  EXPECT_EQ(*here, *under_2005);
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642001).has_value());
}

TEST(SystemVerilog2009KeywordList, IncludesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kSystemVerilog2005AddedKeywords), 97u);
  for (const char* word : kSystemVerilog2005AddedKeywords) {
    auto under_sv2005 = LookupKeyword(word, KeywordVersion::kVer18002005);
    ASSERT_TRUE(under_sv2005.has_value())
        << word << " is one of the words the included list adds";
    if (!under_sv2005.has_value()) continue;

    auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    if (!here.has_value()) continue;
    EXPECT_EQ(*here, *under_sv2005)
        << word << " keeps the same keyword meaning here";

    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642005).has_value())
        << word << " is not reserved by anything that list is built on";
  }
}

TEST(SystemVerilog2009KeywordList,
     AddedWordsAreTheWholeDifferenceFromIncludedLists) {
  EXPECT_EQ(std::size(kSystemVerilog2009AddedKeywords), 23u);
  for (const char* word : kSystemVerilog2009AddedKeywords) {
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002009).has_value())
        << word << " is one of the words this version adds";
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002005).has_value())
        << word << " is not reserved by the last of the included lists";
  }

  size_t newly_reserved = 0;
  auto count_new = [&newly_reserved](const char* word) {
    if (!LookupKeyword(word, KeywordVersion::kVer18002005).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer18002009).has_value()) {
      ++newly_reserved;
    }
  };
  for (const char* word : kVerilog1995Keywords) count_new(word);
  for (const char* word : kVerilog2001AddedKeywords) count_new(word);
  for (const char* word : kVerilog2005AddedKeywords) count_new(word);
  for (const char* word : kSystemVerilog2005AddedKeywords) count_new(word);
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

TEST(SystemVerilog2009KeywordList, TheListIsTheFiveTablesTogether) {
  ExpectTablesPartitionTheList(
      {kVerilog1995KeywordSweep, kVerilog2001AddedKeywordSweep,
       kVerilog2005AddedKeywordSweep, kSystemVerilog2005AddedKeywordSweep,
       kSystemVerilog2009AddedKeywordSweep},
      244);
}

TEST(SystemVerilog2009KeywordList, WordsOutsideTheFiveTablesAreNotReserved) {
  const char* const kLater[] = {
      "implements",
      "interconnect",
      "nettype",
      "soft",
  };
  for (const char* word : kLater) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002009).has_value())
        << word << " belongs to a list later than the five this one names";
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002012).has_value())
        << word << " is reserved by the version after this one";
  }

  const char* const kNotWords[] = {
      "accepts_on", "s_until_without", "unique1", "checkers", "untype",
  };
  for (const char* word : kNotWords) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002009).has_value())
        << word << " is not one of the identifiers Table 22-5 lists";
  }
}

}  // namespace
