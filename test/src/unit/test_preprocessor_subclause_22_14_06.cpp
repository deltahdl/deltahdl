#include <gtest/gtest.h>

#include <iterator>
#include <string>

#include "common/diagnostic.h"
#include "fixture_preprocessor.h"
#include "helpers_keyword_version.h"
#include "lexer/keywords.h"
#include "lexer/token.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

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

TEST(KeywordVersionPreprocessing,
     SystemVerilog2005OnlyTheExactSpecifierSelectsIt) {
  EXPECT_EQ(KindAfterSpecifier("1800-2005", "checker"), TokenKind::kIdentifier);

  const char* const kNearMisses[] = {
      "1800-2004", "1800-2006", "1800_2005", "18002005", "1800-05",
  };
  for (const char* spec : kNearMisses) {
    EXPECT_EQ(KindAfterSpecifier(spec, "checker"), TokenKind::kKwChecker)
        << spec << " names no version, so this list was never put in force";
  }
}

TEST(KeywordVersionPreprocessing,
     SystemVerilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto here = KindInRegion("1800-2005", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

TEST(KeywordVersionPreprocessing,
     SystemVerilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywordTokens), 21u);
  for (const auto& word : kVerilog2001AddedKeywordTokens) {
    EXPECT_EQ(KindInRegion("1800-2005", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the second included list";
  }
}

TEST(KeywordVersionPreprocessing, SystemVerilog2005ReservesTheVerilog2005Word) {
  EXPECT_EQ(KindInRegion("1800-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing, SystemVerilog2005ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kSystemVerilog2005AddedKeywordTokens), 97u);
  for (const auto& word : kSystemVerilog2005AddedKeywordTokens) {
    EXPECT_EQ(KindInRegion("1800-2005", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-2005", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of this version, not an inheritance";
  }
}

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
