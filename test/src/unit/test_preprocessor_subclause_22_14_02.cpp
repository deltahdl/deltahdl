#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

constexpr const char* kWordsAddedAfterVerilog1995[] = {
    "automatic", "generate", "genvar",  "localparam", "signed", "unsigned",
    "uwire",     "logic",    "bit",     "int",        "byte",   "string",
    "interface", "class",    "package", "typedef",    "enum",   "always_comb",
    "checker",   "let",      "global",  "until",      "soft",   "nettype",
};

TokenKind KindOfWordIn(const std::string& src, const std::string& word) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<preprocessed>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  return TokenKind::kError;
}

TokenKind KindInsideRegion(const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n" + word + "\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << word;
  return KindOfWordIn(out, word);
}

TokenKind KindUnderDefaultList(const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(word + "\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << word;
  return KindOfWordIn(out, word);
}

TEST(KeywordVersionPreprocessing, Verilog1995DirectiveEmitsItsVersionMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n"
      "reg logic;\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  ASSERT_LT(pos + 1, out.size());
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13641995);

  EXPECT_EQ(KindOfWordIn(out, "reg"), TokenKind::kKwReg);
  EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing,
     EveryVerilog1995WordStaysReservedInTheRegion) {
  for (const char* word : kVerilog1995Keywords) {
    auto in_region = KindInsideRegion(word);
    auto by_default = KindUnderDefaultList(word);
    EXPECT_NE(in_region, TokenKind::kIdentifier) << word;
    EXPECT_NE(in_region, TokenKind::kError) << word;
    EXPECT_EQ(in_region, by_default) << word;
  }
}

TEST(KeywordVersionPreprocessing,
     WordsOutsideVerilog1995ListBecomeIdentifiers) {
  for (const char* word : kWordsAddedAfterVerilog1995) {
    EXPECT_EQ(KindInsideRegion(word), TokenKind::kIdentifier) << word;
    EXPECT_NE(KindUnderDefaultList(word), TokenKind::kIdentifier) << word;
  }
}

TEST(KeywordVersionPreprocessing,
     NearMissSpecifierDoesNotSelectVerilog1995List) {
  const char* const kNearMisses[] = {"1364-95",    "1995",      "1364-1995 ",
                                     " 1364-1995", "1364_1995", "1364-1996"};
  for (const char* spec : kNearMisses) {
    PreprocFixture f;
    auto out = Preprocess(std::string("`begin_keywords \"") + spec +
                              "\"\n"
                              "reg logic;\n"
                              "`end_keywords\n",
                          f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("unrecognized version specifier: \"") + spec + "\"", 1,
        "22.14"))
        << spec;
    EXPECT_EQ(out.find(kKeywordMarker), std::string::npos) << spec;
    EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kKwLogic) << spec;
  }
}

}  // namespace
