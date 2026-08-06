#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_keyword_version.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// The directive carrying this version_specifier to the stage that applies it.
// The list is selected by name in the source and travels to the lexer as the
// marker the preprocessor emits, so the byte written has to be this version's
// and not the one belonging to the Verilog standard of the same year.
TEST(KeywordVersionPreprocessing, SystemVerilog2005DirectiveEmitsItsOwnMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2005\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002005);

  PreprocFixture same_year;
  auto other = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
      "x\n"
      "`end_keywords\n",
      same_year);
  auto other_pos = other.find(kKeywordMarker);
  ASSERT_NE(other_pos, std::string::npos);
  EXPECT_NE(out[pos + 1], other[other_pos + 1]);
}

// The negative for the specifier, driven from real source rather than from a
// direct call on the string. Only the exact spelling names this list, so a word
// differing from it by its year or by a separator selects nothing and leaves
// the source that follows to be read under whatever list was already in force.
// `checker` is what makes that visible: this version leaves it an ordinary
// identifier while the default list reserves it, so the kind it lexes with says
// which of the two governed the region.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2005OnlyTheExactSpecifierSelectsIt) {
  // The spelling this subclause defines: the word is free.
  EXPECT_EQ(KindAfterSpecifier("1800-2005", "checker"), TokenKind::kIdentifier);

  const char* const kNearMisses[] = {
      "1800-2004", "1800-2006", "1800_2005", "18002005", "1800-05",
  };
  for (const char* spec : kNearMisses) {
    EXPECT_EQ(KindAfterSpecifier(spec, "checker"), TokenKind::kKwChecker)
        << spec << " names no version, so this list was never put in force";
  }
}

// The first included list carried through a real region, swept whole. Each word
// arrives at the lexer holding the keyword it holds under the list it comes
// from, which is what including the identifiers of "1364-1995" amounts to once
// the directive is in force.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto here = KindInRegion("1800-2005", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

// The second included list the same way, and with the keyword named outright.
// The paired leg under "1364-1995" is what makes each of these an inclusion:
// under the earlier list the very same word is an ordinary identifier, so its
// being a keyword here comes from the second list this version names.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const auto& word : kTable222) {
    EXPECT_EQ(KindInRegion("1800-2005", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the second included list";
  }
}

// The third included list, which holds one word. Both of the lists that one is
// built on leave it an identifier, so its being a keyword here traces to the
// third inclusion and to nothing else.
TEST(KeywordVersionPreprocessing, SystemVerilog2005ReservesTheVerilog2005Word) {
  EXPECT_EQ(KindInRegion("1800-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

// Table 22-4 driven through the directive, swept whole and word by word. Each
// entry reaches the lexer as the keyword it names, and the paired leg under
// "1364-2005" -- the union of everything this version includes -- has the very
// same word arriving as an ordinary identifier. That pairing is the claim: the
// words are additions of this version_specifier rather than anything inherited.
TEST(KeywordVersionPreprocessing, SystemVerilog2005ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kTable224), 97u);
  for (const auto& word : kTable224) {
    EXPECT_EQ(KindInRegion("1800-2005", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-2005", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of this version, not an inheritance";
  }
}

// The negative the four tables imply: a word none of them lists reaches the
// lexer as an ordinary identifier under this version, however firmly a later
// standard reserves it.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2005LeavesLaterWordsAsIdentifiers) {
  const char* const kLater[] = {
      "accept_on", "checker", "endchecker",   "eventually", "global",
      "let",       "until",   "untyped",      "weak",       "unique0",
      "nettype",   "soft",    "interconnect", "implements", "restrict",
  };
  for (const char* word : kLater) {
    EXPECT_EQ(KindInRegion("1800-2005", word), TokenKind::kIdentifier)
        << word << " is outside the four tables this version names";
  }
}

}  // namespace
