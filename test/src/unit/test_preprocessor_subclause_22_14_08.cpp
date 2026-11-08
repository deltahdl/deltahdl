#include <gtest/gtest.h>

#include <iterator>
#include <string>

#include "common/diagnostic.h"
#include "fixture_preprocessor.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"
#include "lexer/token.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

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

  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2012\"\ninterconnect\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find(kKeywordMarker), std::string::npos);
}

TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto here = KindInRegion("1800-2012", word);
    EXPECT_NE(here, TokenKind::kIdentifier) << word << " is a reserved word";
    EXPECT_EQ(here, KindInRegion("1364-1995", word))
        << word << " keeps its meaning from the list it comes from";
  }
}

TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywordTokens), 21u);
  for (const auto& word : kVerilog2001AddedKeywordTokens) {
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

TEST(KeywordVersionPreprocessing, SystemVerilog2012ReservesTheVerilog2005Word) {
  EXPECT_EQ(KindInRegion("1800-2012", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2005", "uwire"), TokenKind::kKwUwire);
  EXPECT_EQ(KindInRegion("1364-2001", "uwire"), TokenKind::kIdentifier);
  EXPECT_EQ(KindInRegion("1364-1995", "uwire"), TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEverySystemVerilog2005Keyword) {
  EXPECT_EQ(std::size(kSystemVerilog2005AddedKeywordTokens), 97u);
  for (const auto& word : kSystemVerilog2005AddedKeywordTokens) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1364-2005", word.text), TokenKind::kIdentifier)
        << word.text << " comes from the fourth included list";
  }
}

TEST(KeywordVersionPreprocessing,
     SystemVerilog2012ReservesEverySystemVerilog2009Keyword) {
  EXPECT_EQ(std::size(kSystemVerilog2009AddedKeywordTokens), 23u);
  for (const auto& word : kSystemVerilog2009AddedKeywordTokens) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1800-2005", word.text), TokenKind::kIdentifier)
        << word.text << " comes from the fifth included list";
  }
}

TEST(KeywordVersionPreprocessing, SystemVerilog2012ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kSystemVerilog2012AddedKeywordTokens), 4u);
  for (const auto& word : kSystemVerilog2012AddedKeywordTokens) {
    EXPECT_EQ(KindInRegion("1800-2012", word.text), word.kind) << word.text;
    EXPECT_EQ(KindInRegion("1800-2009", word.text), TokenKind::kIdentifier)
        << word.text << " is an addition of this version, not an inheritance";
  }
}

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
