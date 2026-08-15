#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// The directive carrying this version_specifier to the stage that applies it.
// The list is selected by name in the source and travels to the lexer as the
// marker the preprocessor emits, so the byte written has to be this version's
// and not that of the SystemVerilog standard on either side of it.
TEST(KeywordVersionPreprocessing, SystemVerilog2012DirectiveEmitsItsOwnMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2012\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002012);

  for (const char* neighbour : {"1800-2009", "1800-2017"}) {
    PreprocFixture other_fixture;
    auto other = Preprocess(std::string("`begin_keywords \"") + neighbour +
                                "\"\nx\n`end_keywords\n",
                            other_fixture);
    auto other_pos = other.find(kKeywordMarker);
    ASSERT_NE(other_pos, std::string::npos) << neighbour;
    EXPECT_NE(out[pos + 1], other[other_pos + 1]) << neighbour;
  }
}

// The negative for the specifier, driven from real source rather than from a
// direct call on the string. Only the exact spelling names this list: a word
// differing from it by its year or by a separator selects nothing, so no marker
// carrying this version is written at all and the source that follows is left
// to whatever list was already in force.
//
// The earlier versions in this ladder can show that by pointing at a word the
// misspelt region leaves reserved and this one does not. This version cannot --
// it reserves everything the default list does -- so what is read instead is
// the marker itself, which is the whole of what the directive contributes to
// the stage below.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2012OnlyTheExactSpecifierSelectsIt) {
  const char* const kNearMisses[] = {
      "1800-2011", "1800-2013", "1800_2012", "18002012", "1364-2012",
  };
  for (const char* spec : kNearMisses) {
    PreprocFixture f;
    auto out = Preprocess(std::string("`begin_keywords \"") + spec +
                              "\"\ninterconnect\n`end_keywords\n",
                          f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("unrecognized version specifier: \"") + spec + "\"", 1,
        "22.14"))
        << spec << " names no version this implementation knows";
    EXPECT_EQ(out.find(kKeywordMarker), std::string::npos)
        << spec << " opened no region, so no list was put in force";
  }

  // The control: the spelling this subclause defines does write the marker, so
  // the absences above are the misspelling and not the source shape.
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2012\"\ninterconnect\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find(kKeywordMarker), std::string::npos);
}

// The first included list carried through a real region, swept whole. Each word
// arrives at the lexer holding the keyword it holds under the list it comes
// from, which is what including the identifiers of "1364-1995" amounts to once
// the directive is in force.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto here = KindInRegion("1800-2012", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

// The second included list the same way, and with the keyword named outright.
// The leg under "1364-1995" is what makes each of these an inclusion: under the
// earlier list the very same word is an ordinary identifier. The ten
// configuration words carry a second leg of their own, under the
// configuration-free companion list that drops exactly them -- which is how the
// region shows that this version inherits "1364-2001" whole rather than its
// reduced companion.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const auto& word : kTable222) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the second included list";
  }

  for (const char* word : kConfigurationWords) {
    EXPECT_NE(KindInRegion("1800-2012", word), TokenKind::kIdentifier) << word;
    EXPECT_EQ(KindInRegion("1364-2001-noconfig", word), TokenKind::kIdentifier)
        << word << " is what the configuration-free companion list drops";
  }
}

// The third included list, which holds one word. Both of the lists that one is
// built on leave it an identifier, so its being a keyword here traces to the
// third inclusion and to nothing else.
TEST(KeywordVersionPreprocessing, SystemVerilog2012ReservesTheVerilog2005Word) {
  EXPECT_EQ(KindInRegion("1800-2012", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

// The fourth included list driven through the directive, swept whole. Each
// entry reaches the lexer as the keyword it names, and under "1364-2005" -- the
// union of the three lists that one is itself built on -- the very same word
// arrives as an ordinary identifier, so the inclusion is the fourth one rather
// than anything earlier.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kTable224), 97u);
  for (const auto& word : kTable224) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-2005", word.text), TokenKind::kIdentifier)
        << word.text << " comes from the fourth included list";
  }
}

// The fifth included list the same way -- the last one before this version's
// own. Under "1800-2005", the union of the four lists it is built on, every one
// of its entries arrives as an ordinary identifier.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEverySystemVerilog2009Keyword) {
  EXPECT_EQ(std::size(kTable225), 23u);
  for (const auto& word : kTable225) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1800-2005", word.text), TokenKind::kIdentifier)
        << word.text << " comes from the fifth included list";
  }
}

// Table 22-6 driven through the directive, word by word. Each entry reaches the
// lexer as the keyword it names, and the paired leg under "1800-2009" -- the
// union of everything this version includes -- has the very same word arriving
// as an ordinary identifier. That pairing is the claim: the words are additions
// of this version_specifier rather than anything inherited.
TEST(KeywordVersionPreprocessing, SystemVerilog2012ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kTable226), 4u);
  for (const auto& word : kTable226) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1800-2009", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of this version, not an inheritance";
  }
}

// The negative the six tables imply, at the stage that puts the list in force:
// a word none of them holds reaches the lexer as an ordinary identifier here.
// Each is a near miss of a real entry -- differing by a prefix, a suffix, or a
// separator -- so what is bounded is the table's own membership rather than the
// vocabulary at large.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2012LeavesWordsOutsideTheTablesAsIdentifiers) {
  const char* const kNotWords[] = {
      "implement", "implements_", "interconnects", "inter_connect", "nettypes",
      "net_type",  "softly",      "soft_",         "endnettype",
  };
  for (const char* word : kNotWords) {
    EXPECT_EQ(KindInRegion("1800-2012", word), TokenKind::kIdentifier)
        << word << " is outside the six tables this version names";
  }
}

}  // namespace
