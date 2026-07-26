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

// The ten of Table 22-2 that the configuration-free companion list drops.
constexpr const char* kConfigurationWords[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

// The same, for a specifier string that may not name any version at all. The
// diagnostics are read but not asserted on -- whether an unrecognized string is
// an error is settled elsewhere; what matters here is only which reserved word
// list the source that follows ends up being read under.
TokenKind KindAfterSpecifier(const std::string& spec, const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + spec + "\"\n" + word + "\n`end_keywords\n", f);

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  ADD_FAILURE() << word << " never reached the token stream";
  return TokenKind::kError;
}

// The directive carrying this version_specifier to the stage that applies it.
// The list is selected by name in the source and travels to the lexer as the
// marker the preprocessor emits, so the byte written has to be this version's
// and not that of the SystemVerilog standard on either side of it.
TEST(KeywordVersionPreprocessing, SystemVerilog2009DirectiveEmitsItsOwnMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2009\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);

  for (const char* neighbour : {"1800-2005", "1800-2012"}) {
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
// direct call on the string. Only the exact spelling names this list, so a word
// differing from it by its year or by a separator selects nothing and leaves
// the source that follows to be read under whatever list was already in force.
// `interconnect` is what makes that visible: this version leaves it an ordinary
// identifier while the default list reserves it, so the kind it lexes with says
// which of the two governed the region.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009OnlyTheExactSpecifierSelectsIt) {
  // The spelling this subclause defines: the word is free.
  EXPECT_EQ(KindAfterSpecifier("1800-2009", "interconnect"),
            TokenKind::kIdentifier);

  const char* kNearMisses[] = {
      "1800-2008", "1800-2010", "1800_2009", "18002009", "1364-2009",
  };
  for (const char* spec : kNearMisses) {
    EXPECT_EQ(KindAfterSpecifier(spec, "interconnect"),
              TokenKind::kKwInterconnect)
        << spec << " names no version, so this list was never put in force";
  }
}

// The first included list carried through a real region, swept whole. Each word
// arrives at the lexer holding the keyword it holds under the list it comes
// from, which is what including the identifiers of "1364-1995" amounts to once
// the directive is in force.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto here = KindInRegion("1800-2009", word);
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
     SystemVerilog2009ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const auto& word : kTable222) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the second included list";
  }

  for (const char* word : kConfigurationWords) {
    EXPECT_NE(KindInRegion("1800-2009", word), TokenKind::kIdentifier) << word;
    EXPECT_EQ(KindInRegion("1364-2001-noconfig", word), TokenKind::kIdentifier)
        << word << " is what the configuration-free companion list drops";
  }
}

// The third included list, which holds one word. Both of the lists that one is
// built on leave it an identifier, so its being a keyword here traces to the
// third inclusion and to nothing else.
TEST(KeywordVersionPreprocessing, SystemVerilog2009ReservesTheVerilog2005Word) {
  EXPECT_EQ(KindInRegion("1800-2009", "uwire"), TokenKind::kKwUwire);
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
     SystemVerilog2009ReservesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kTable224), 97u);
  for (const auto& word : kTable224) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-2005", word.text), TokenKind::kIdentifier)
        << word.text << " comes from the fourth included list";
  }
}

// Table 22-5 driven through the directive, swept whole and word by word. Each
// entry reaches the lexer as the keyword it names, and the paired leg under
// "1800-2005" -- the union of everything this version includes -- has the very
// same word arriving as an ordinary identifier. That pairing is the claim: the
// words are additions of this version_specifier rather than anything inherited.
TEST(KeywordVersionPreprocessing, SystemVerilog2009ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kTable225), 23u);
  for (const auto& word : kTable225) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1800-2005", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of this version, not an inheritance";
  }
}

// The negative the five tables imply: a word none of them lists reaches the
// lexer as an ordinary identifier under this version, however firmly the next
// standard reserves it. Each is paired against that later specifier so the
// words are seen to be later ones rather than merely unknown ones.
TEST(KeywordVersionPreprocessing,
     SystemVerilog2009LeavesLaterWordsAsIdentifiers) {
  struct LaterWord {
    const char* text;
    TokenKind kind;
  };
  const LaterWord kLater[] = {
      {"implements", TokenKind::kKwImplements},
      {"interconnect", TokenKind::kKwInterconnect},
      {"nettype", TokenKind::kKwNettype},
      {"soft", TokenKind::kKwSoft},
  };
  for (const auto& word : kLater) {
    EXPECT_EQ(KindInRegion("1800-2009", word.text), TokenKind::kIdentifier)
        << word.text << " is outside the five tables this version names";
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind)
        << word.text << " is reserved by the version after this one";
  }
}

}  // namespace
