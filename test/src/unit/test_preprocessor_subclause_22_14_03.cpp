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

constexpr const char* kNotIn2001[] = {
    "uwire",        "logic",      "bit",         "int",    "byte",
    "string",       "var",        "interface",   "class",  "package",
    "typedef",      "enum",       "always_comb", "assert", "checker",
    "let",          "global",     "until",       "soft",   "nettype",
    "interconnect", "implements",
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

TokenKind KindInRegion(const char* version, const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(std::string("`begin_keywords \"") + version + "\"\n" +
                            word + "\n`end_keywords\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors()) << word;
  return KindOfWordIn(out, word);
}

TokenKind KindUnderDefaultList(const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(word + "\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << word;
  return KindOfWordIn(out, word);
}

TEST(KeywordVersionPreprocessing, Verilog2001DirectiveEmitsItsVersionMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "genvar logic;\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  ASSERT_LT(pos + 1, out.size());
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642001);

  EXPECT_EQ(KindOfWordIn(out, "genvar"), TokenKind::kKwGenvar);
  EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kIdentifier);
}

TEST(KeywordVersionPreprocessing, Verilog2001AdditionsAreReservedInTheRegion) {
  for (const char* word : kVerilog2001AddedKeywords) {
    auto in_region = KindInRegion("1364-2001", word);
    EXPECT_NE(in_region, TokenKind::kIdentifier) << word;
    EXPECT_NE(in_region, TokenKind::kError) << word;
    EXPECT_EQ(in_region, KindUnderDefaultList(word)) << word;
    EXPECT_EQ(KindInRegion("1364-1995", word), TokenKind::kIdentifier)
        << word << " is an addition of this version";
  }
}

TEST(KeywordVersionPreprocessing,
     EveryVerilog1995WordStaysReservedUnderVerilog2001) {
  for (const char* word : kVerilog1995Keywords) {
    auto in_region = KindInRegion("1364-2001", word);
    EXPECT_NE(in_region, TokenKind::kIdentifier) << word;
    EXPECT_NE(in_region, TokenKind::kError) << word;
    EXPECT_EQ(in_region, KindUnderDefaultList(word)) << word;
  }
}

TEST(KeywordVersionPreprocessing,
     WordsOutsideVerilog2001ListBecomeIdentifiers) {
  for (const char* word : kNotIn2001) {
    EXPECT_EQ(KindInRegion("1364-2001", word), TokenKind::kIdentifier) << word;
    EXPECT_NE(KindUnderDefaultList(word), TokenKind::kIdentifier) << word;
  }
}

TEST(KeywordVersionPreprocessing, NearMissSpecifierDoesNotSelectThisList) {
  const char* const kNearMisses[] = {"1364-01",    "2001",      "1364-2001 ",
                                     " 1364-2001", "1364_2001", "1364-2002",
                                     "1364-20001"};
  for (const char* spec : kNearMisses) {
    PreprocFixture f;
    auto out = Preprocess(std::string("`begin_keywords \"") + spec +
                              "\"\n"
                              "genvar logic;\n"
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
