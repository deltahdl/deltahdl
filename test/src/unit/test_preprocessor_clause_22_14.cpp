#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywordsEmitsMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2023\"\n"
      "module t; endmodule\n"
      "`end_keywords\n",
      f);

  size_t first = out.find(kKeywordMarker);
  ASSERT_NE(first, std::string::npos);
  auto ver = static_cast<KeywordVersion>(out[first + 1]);
  EXPECT_EQ(ver, KeywordVersion::kVer18002023);
}

TEST(KeywordVersionPreprocessing, EndKeywordsRestoresDefault) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n"
      "x\n"
      "`end_keywords\n"
      "y\n",
      f);

  size_t first = out.find(kKeywordMarker);
  ASSERT_NE(first, std::string::npos);
  size_t second = out.find(kKeywordMarker, first + 1);
  ASSERT_NE(second, std::string::npos);
  auto ver = static_cast<KeywordVersion>(out[second + 1]);
  EXPECT_EQ(ver, KeywordVersion::kVer18002023);
}

TEST(KeywordVersionPreprocessing, AllVersionSpecifiersRecognized) {
  struct Case {
    const char* spec;
    KeywordVersion expected;
  };
  const Case kCases[] = {
      {"1364-1995", KeywordVersion::kVer13641995},
      {"1364-2001", KeywordVersion::kVer13642001},
      {"1364-2001-noconfig", KeywordVersion::kVer13642001Noconfig},
      {"1364-2005", KeywordVersion::kVer13642005},
      {"1800-2005", KeywordVersion::kVer18002005},
      {"1800-2009", KeywordVersion::kVer18002009},
      {"1800-2012", KeywordVersion::kVer18002012},
      {"1800-2017", KeywordVersion::kVer18002017},
      {"1800-2023", KeywordVersion::kVer18002023},
  };
  for (const auto& c : kCases) {
    PreprocFixture f;
    std::string src = "`begin_keywords \"" + std::string(c.spec) +
                      "\"\n"
                      "x\n`end_keywords\n";
    auto out = Preprocess(src, f);
    EXPECT_FALSE(f.diag.HasErrors()) << c.spec;
    auto pos = out.find(kKeywordMarker);
    ASSERT_NE(pos, std::string::npos) << c.spec;
    auto ver = static_cast<KeywordVersion>(out[pos + 1]);
    EXPECT_EQ(ver, c.expected) << c.spec;
  }
}

TEST(KeywordVersionPreprocessing, ErrorUnrecognizedVersion) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"9999-9999\"\n`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorMissingQuotedString) {
  PreprocFixture f;
  Preprocess("`begin_keywords\n`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorMissingClosingQuote) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"1800-2023\n`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorEndKeywordsWithoutBegin) {
  PreprocFixture f;
  Preprocess("`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorEmptyVersionString) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"\"\n`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, NestedBeginKeywords) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2005\"\n"
      "a\n"
      "`begin_keywords \"1364-1995\"\n"
      "b\n"
      "`end_keywords\n"
      "c\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  size_t pos = 0;
  pos = out.find(kKeywordMarker, pos);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002005);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13641995);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002005);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002023);
}

TEST(KeywordVersionPreprocessing, DoubleNestedBeginKeywords) {
  PreprocFixture f;
  Preprocess(
      "`begin_keywords \"1800-2012\"\n"
      "`begin_keywords \"1800-2005\"\n"
      "`begin_keywords \"1364-2001\"\n"
      "x\n"
      "`end_keywords\n"
      "`end_keywords\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ResetallDoesNotAffectKeywordVersion) {
  PreprocFixture f;
  Preprocess(
      "`begin_keywords \"1364-1995\"\n"
      "`resetall\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorBeginKeywordsInsideDesignElement) {
  PreprocFixture f;
  Preprocess(
      "module m;\n"
      "`begin_keywords \"1800-2023\"\n"
      "`end_keywords\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorEndKeywordsInsideDesignElement) {
  PreprocFixture f;
  Preprocess(
      "`begin_keywords \"1800-2023\"\n"
      "module m;\n"
      "`end_keywords\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, BeginKeywordsInFalseIfdef) {
  PreprocFixture f;
  auto out = Preprocess(
      "`ifdef UNDEFINED\n"
      "`begin_keywords \"1364-1995\"\n"
      "`endif\n"
      "logic x;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
}

TEST(KeywordVersionPreprocessing, LexerSeesVersionSwitch) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "logic\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  bool found_logic = false;
  for (const auto& tok : tokens) {
    if (tok.text == "logic") {
      EXPECT_EQ(tok.kind, TokenKind::kIdentifier);
      found_logic = true;
    }
  }
  EXPECT_TRUE(found_logic);
}

TEST(KeywordVersionPreprocessing, LexerSeesKeywordAfterEndKeywords) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "logic\n"
      "`end_keywords\n"
      "logic\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  std::vector<TokenKind> logic_kinds;
  for (const auto& tok : tokens) {
    if (tok.text == "logic") {
      logic_kinds.push_back(tok.kind);
    }
  }
  ASSERT_EQ(logic_kinds.size(), 2u);
  EXPECT_EQ(logic_kinds[0], TokenKind::kIdentifier);
  EXPECT_EQ(logic_kinds[1], TokenKind::kKwLogic);
}

TEST(KeywordVersionPreprocessing, LogicAsIdentifierUnder1364_2001) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "logic\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  bool found = false;
  for (const auto& tok : tokens) {
    if (tok.text == "logic") {
      EXPECT_EQ(tok.kind, TokenKind::kIdentifier);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(KeywordVersionPreprocessing, InterfaceNotKeywordUnder1364_2005) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
      "interface\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  bool found = false;
  for (const auto& tok : tokens) {
    if (tok.text == "interface") {
      EXPECT_EQ(tok.kind, TokenKind::kIdentifier);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(KeywordVersionPreprocessing, MarkerFormatCorrect) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2009\"\n"
      "`end_keywords\n",
      f);
  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  ASSERT_LT(pos + 2, out.size());
  EXPECT_EQ(out[pos], kKeywordMarker);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);
  EXPECT_EQ(out[pos + 2], '\n');
}

TEST(KeywordVersionPreprocessing, ConsecutiveBeginEndPairs) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-1995\"\n"
      "x\n"
      "`end_keywords\n"
      "`begin_keywords \"1800-2009\"\n"
      "y\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  size_t pos = 0;
  pos = out.find(kKeywordMarker, pos);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13641995);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002023);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002023);
}

TEST(KeywordVersionPreprocessing, BeginKeywordsWhitespaceBeforeQuote) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords   \"1800-2012\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002012);
}

TEST(KeywordVersionPreprocessing, SameVersionNested) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2009\"\n"
      "`begin_keywords \"1800-2009\"\n"
      "x\n"
      "`end_keywords\n"
      "y\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  size_t pos = 0;
  pos = out.find(kKeywordMarker, pos);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002009);

  pos = out.find(kKeywordMarker, pos + 1);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002023);
}

}  // namespace
