#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_lexer.h"
#include "lexer/keywords.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// The spelling of the version_specifier is what selects this list, so the
// string has to resolve to its own version and to nothing else. The two
// neighbours it is most easily confused with are the version it extends and the
// SystemVerilog standard published the same year.
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

// The negative for that spelling. A version_specifier is a fixed string, so a
// word differing from it by case, by a separator, by surrounding space, or by
// its year is not this one and names no list at all.
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

// The first list this version includes, swept whole rather than sampled. Each
// word is read under both versions from the same lookup, so "1364-1995" is the
// baseline the inclusion is measured against instead of an assumption, and the
// keyword each word resolves to has to be the same one -- being reserved for a
// different meaning would not be inclusion.
TEST(Verilog2005KeywordList, IncludesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
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

// The second list this version includes, swept whole and read the same way.
// This one is included entire: the ten configuration words a neighbouring
// version_specifier drops are reserved here along with the other eleven.
TEST(Verilog2005KeywordList, IncludesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222Words), 21u);
  for (const char* word : kTable222Words) {
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

// The word this version contributes on its own, and what makes it an
// *addition* rather than something inherited: it is reserved here and is an
// ordinary identifier under both of the lists this version includes. The sweep
// over those two lists is the other half of the claim -- across every word they
// contain, being reserved here but not under "1364-2001" happens for this word
// and for no other, so Table 22-3 accounts for the whole difference.
TEST(Verilog2005KeywordList, AddsExactlyOneWordOfItsOwn) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* added = kTable223[0];

  auto here = LookupKeyword(added, KeywordVersion::kVer13642005);
  ASSERT_TRUE(here.has_value());
  if (!here.has_value()) return;
  EXPECT_EQ(*here, TokenKind::kKwUwire);

  EXPECT_FALSE(LookupKeyword(added, KeywordVersion::kVer13641995).has_value())
      << added << " is not reserved by the earlier of the two included lists";
  EXPECT_FALSE(LookupKeyword(added, KeywordVersion::kVer13642001).has_value())
      << added << " is not reserved by the later of the two included lists";

  size_t newly_reserved = 0;
  for (const char* word : kTable221) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642001).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer13642005).has_value()) {
      ++newly_reserved;
    }
  }
  for (const char* word : kTable222Words) {
    if (!LookupKeyword(word, KeywordVersion::kVer13642001).has_value() &&
        LookupKeyword(word, KeywordVersion::kVer13642005).has_value()) {
      ++newly_reserved;
    }
  }
  EXPECT_EQ(newly_reserved, 0u)
      << "the included lists contribute nothing this version reserves anew";
}

// The three tables put together are the list, so their sizes add up to it and
// none of them repeats a word another already holds. Without this the sweeps
// above could each pass while between them covering only part of the list.
TEST(Verilog2005KeywordList, TheListIsTheThreeTablesTogether) {
  EXPECT_EQ(
      std::size(kTable221) + std::size(kTable222Words) + std::size(kTable223),
      124u);

  auto in_table221 = [](const std::string& word) {
    for (const char* w : kTable221) {
      if (word == w) return true;
    }
    return false;
  };
  for (const char* word : kTable222Words) {
    EXPECT_FALSE(in_table221(word)) << word << " is counted twice";
  }
  for (const char* word : kTable223) {
    EXPECT_FALSE(in_table221(word)) << word << " is counted twice";
    for (const char* w : kTable222Words) {
      EXPECT_NE(std::string(word), w) << word << " is counted twice";
    }
  }
}

// The list bounds what is reserved from above as well as from below: naming
// three tables says nothing outside them is a reserved word here. The words a
// later standard introduces are the ones this matters for, and they stay
// unreserved under this version.
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
