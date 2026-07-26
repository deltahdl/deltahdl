#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_lexer.h"
#include "helpers_keyword_table_partition.h"
#include "lexer/keywords.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// The spelling of the version_specifier is what selects this list, so the
// string has to resolve to its own version and to nothing else. Its two nearest
// neighbours are the SystemVerilog standards on either side of it, each
// differing only in the year.
TEST(SystemVerilog2009KeywordList, SpecifierResolvesToItsOwnVersion) {
  auto parsed = ParseKeywordVersion("1800-2009");
  ASSERT_TRUE(parsed.has_value());
  EXPECT_EQ(*parsed, KeywordVersion::kVer18002009);

  auto previous = ParseKeywordVersion("1800-2005");
  ASSERT_TRUE(previous.has_value());
  EXPECT_NE(*parsed, *previous);

  auto next_standard = ParseKeywordVersion("1800-2012");
  ASSERT_TRUE(next_standard.has_value());
  EXPECT_NE(*parsed, *next_standard);
}

// The negative for that spelling. A version_specifier is a fixed string, so a
// word differing from it by a separator, by surrounding space, or by its year
// or standard number is not this one and names no list at all.
TEST(SystemVerilog2009KeywordList, SpecifierMisspellingsAreNotRecognized) {
  const char* kNotThisSpecifier[] = {
      "1800-2009 ", " 1800-2009", "1800_2009", "18002009", "1800-2010",
      "1800-2008",  "1800-09",    "1364-2009", "2009",     "1800-2009-noconfig",
  };
  for (const char* spec : kNotThisSpecifier) {
    EXPECT_FALSE(ParseKeywordVersion(spec).has_value())
        << spec << " is not the spelling this subclause defines";
  }
}

// The first included list, swept whole rather than sampled. Each word is read
// under both versions from the same lookup, so "1364-1995" is the baseline the
// inclusion is measured against instead of an assumption, and the keyword each
// word resolves to has to be the same one -- being reserved for a different
// meaning would not be inclusion.
TEST(SystemVerilog2009KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto under_1995 = LookupKeyword(word, KeywordVersion::kVer13641995);
    ASSERT_TRUE(under_1995.has_value())
        << word << " is one of the words the included list reserves";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_1995)
        << word << " keeps the same keyword meaning here";
  }
}

// The second included list, swept the same way. "All previous versions"
// includes two lists published for the same standard -- one with the
// configuration words and one without -- and this test settles which of them
// governs: all twenty-one entries are reserved here, and the ten the
// configuration-free list drops are called out on their own, since they are the
// only entries on which the two disagree.
TEST(SystemVerilog2009KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222Words), 21u);
  for (const char* word : kTable222Words) {
    auto under_2001 = LookupKeyword(word, KeywordVersion::kVer13642001);
    ASSERT_TRUE(under_2001.has_value())
        << word << " is one of the words the included list adds";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
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

// The third included list, which holds one word. It is reserved here with the
// meaning it has under the list it comes from, and it is not reserved by either
// of the two lists that one is itself built on -- so its being a keyword here
// can only have come from the third inclusion.
TEST(SystemVerilog2009KeywordList, IncludesTheVerilog2005Keyword) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* word = kTable223[0];

  auto under_2005 = LookupKeyword(word, KeywordVersion::kVer13642005);
  ASSERT_TRUE(under_2005.has_value());

  auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
  ASSERT_TRUE(here.has_value());
  EXPECT_EQ(*here, *under_2005);
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13641995).has_value());
  EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642001).has_value());
}

// The fourth included list, swept whole. Its entries are reserved here with the
// meaning they carry under the list they come from, and each is an ordinary
// identifier under "1364-2005" -- the union of the three lists that one is
// itself built on -- so their being keywords here traces to the fourth
// inclusion and to nothing earlier.
TEST(SystemVerilog2009KeywordList, IncludesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kTable224Words), 97u);
  for (const char* word : kTable224Words) {
    auto under_sv2005 = LookupKeyword(word, KeywordVersion::kVer18002005);
    ASSERT_TRUE(under_sv2005.has_value())
        << word << " is one of the words the included list adds";

    auto here = LookupKeyword(word, KeywordVersion::kVer18002009);
    ASSERT_TRUE(here.has_value()) << word << " is included by this version";
    EXPECT_EQ(*here, *under_sv2005)
        << word << " keeps the same keyword meaning here";

    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer13642005).has_value())
        << word << " is not reserved by anything that list is built on";
  }
}

// Table 22-5 and what makes its entries *additions* rather than inheritances:
// each is reserved here and is an ordinary identifier under the last of the
// four lists this version includes, which is the union of all four. The sweep
// over those four lists is the other half of the claim -- across every word
// they hold, being reserved here but not under "1800-2005" happens for none of
// them, so Table 22-5 accounts for the whole difference between the two lists.
TEST(SystemVerilog2009KeywordList,
     AddedWordsAreTheWholeDifferenceFromIncludedLists) {
  EXPECT_EQ(std::size(kTable225Words), 23u);
  for (const char* word : kTable225Words) {
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
  for (const char* word : kTable221) count_new(word);
  for (const char* word : kTable222Words) count_new(word);
  for (const char* word : kTable223) count_new(word);
  for (const char* word : kTable224Words) count_new(word);
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

// The five tables put together are the list, so their sizes add up to it and
// none of them repeats a word another already holds. Without this the sweeps
// above could each pass while between them covering only part of the list.
TEST(SystemVerilog2009KeywordList, TheListIsTheFiveTablesTogether) {
  ExpectTablesPartitionTheList({kSweepTable221, kSweepTable222, kSweepTable223,
                                kSweepTable224, kSweepTable225},
                               244);
}

// The list bounds what is reserved from above as well as from below: naming
// four included tables plus one of its own says nothing outside them is a
// reserved word here. The words the next standard introduces are what this
// matters for, and they stay unreserved under this version.
TEST(SystemVerilog2009KeywordList, WordsOutsideTheFiveTablesAreNotReserved) {
  const char* kLater[] = {
      "implements",
      "interconnect",
      "nettype",
      "soft",
  };
  for (const char* word : kLater) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002009).has_value())
        << word << " belongs to a list later than the five this one names";
    // The pairing is what makes each a *later* word rather than one that is
    // simply unknown: the next standard's specifier does reserve it.
    EXPECT_TRUE(LookupKeyword(word, KeywordVersion::kVer18002012).has_value())
        << word << " is reserved by the version after this one";
  }

  // Near-misses on this version's own additions, which no table lists.
  const char* kNotWords[] = {
      "accepts_on", "s_until_without", "unique1", "checkers", "untype",
  };
  for (const char* word : kNotWords) {
    EXPECT_FALSE(LookupKeyword(word, KeywordVersion::kVer18002009).has_value())
        << word << " is not one of the identifiers Table 22-5 lists";
  }
}

}  // namespace
