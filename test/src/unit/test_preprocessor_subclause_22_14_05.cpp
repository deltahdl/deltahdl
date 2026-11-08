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

TEST(KeywordVersionPreprocessing, Verilog2005DirectiveEmitsItsOwnMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642005);

  PreprocFixture extended;
  auto other = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "x\n"
      "`end_keywords\n",
      extended);
  auto other_pos = other.find(kKeywordMarker);
  ASSERT_NE(other_pos, std::string::npos);
  EXPECT_NE(out[pos + 1], other[other_pos + 1]);
}

TEST(KeywordVersionPreprocessing, Verilog2005OnlyTheExactSpecifierSelectsIt) {
  EXPECT_EQ(KindAfterSpecifier("1364-2005", "logic"), TokenKind::kIdentifier);

  const char* const kNearMisses[] = {
      "1364-2004", "1364-2006", "1364_2005", "13642005", "1364-05",
  };
  for (const char* spec : kNearMisses) {
    EXPECT_EQ(KindAfterSpecifier(spec, "logic"), TokenKind::kKwLogic)
        << spec << " names no version, so this list was never put in force";
  }
}

TEST(KeywordVersionPreprocessing, Verilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto here = KindInRegion("1364-2005", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

TEST(KeywordVersionPreprocessing, Verilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywordTokens), 21u);
  for (const auto& word : kVerilog2001AddedKeywordTokens) {
    EXPECT_EQ(KindInRegion("1364-2005", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-1995", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of the later of the two lists";
  }
}

TEST(KeywordVersionPreprocessing, Verilog2005ReservesTheWordItAddsItself) {
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing, Verilog2005LeavesLaterWordsAsIdentifiers) {
  const char* const kLater[] = {
      "logic",   "interface", "endinterface", "bit",     "byte",
      "int",     "longint",   "always_comb",  "package", "class",
      "typedef", "enum",      "string",       "nettype", "checker",
  };
  for (const char* word : kLater) {
    EXPECT_EQ(KindInRegion("1364-2005", word), TokenKind::kIdentifier)
        << word << " is outside the three tables this version names";
  }
}

}  // namespace
