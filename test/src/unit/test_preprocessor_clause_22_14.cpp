#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string &src, PreprocFixture &f,
                              PreprocConfig config = {}) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  return pp.Preprocess(fid);
}

// --- begin_keywords / end_keywords tests (IEEE 1800-2023 §22.14) ---

TEST(Preprocessor, BeginKeywords_EmitsMarker) {
  PreprocFixture f;
  auto result = Preprocess("`begin_keywords \"1364-2001\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Marker: \x01 + version byte (1 = kVer13642001) + \n
  std::string expected = {kKeywordMarker, '\x01', '\n'};
  EXPECT_NE(result.find(expected), std::string::npos);
}

TEST(Preprocessor, EndKeywords_EmitsRestoreMarker) {
  PreprocFixture f;
  auto result = Preprocess("`begin_keywords \"1364-2001\"\n"
                           "`end_keywords\n",
                           f);
  EXPECT_FALSE(f.diag.HasErrors());
  // After end_keywords with empty stack, restores to kVer18002023 (8).
  std::string restore = {kKeywordMarker, '\x08', '\n'};
  EXPECT_NE(result.find(restore), std::string::npos);
}

TEST(Preprocessor, BeginKeywords_InvalidVersion) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"bogus\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, EndKeywords_WithoutBegin) {
  PreprocFixture f;
  Preprocess("`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, BeginKeywords_NestedRestoresVersion) {
  PreprocFixture f;
  auto result = Preprocess("`begin_keywords \"1364-2001\"\n"
                           "`begin_keywords \"1800-2005\"\n"
                           "`end_keywords\n"
                           "`end_keywords\n",
                           f);
  EXPECT_FALSE(f.diag.HasErrors());
  // First begin: version 1 (1364-2001)
  std::string m1 = {kKeywordMarker, '\x01', '\n'};
  // Second begin: version 4 (1800-2005)
  std::string m2 = {kKeywordMarker, '\x04', '\n'};
  // Second end: restore to 8 (1800-2023)
  std::string m4 = {kKeywordMarker, '\x08', '\n'};
  EXPECT_NE(result.find(m1), std::string::npos);
  EXPECT_NE(result.find(m2), std::string::npos);
  // First end restores to version 1, same as m1 — already verified.
  EXPECT_NE(result.find(m4), std::string::npos);
}

// --- Preprocessor+Lexer integration tests from test_lexical.cpp ---

TEST(Preprocessor, BeginKeywords_LogicAsIdentifier) {
  PreprocFixture f;
  auto preprocessed = Preprocess("`begin_keywords \"1364-2001\"\n"
                                 "module m; reg logic; endmodule\n"
                                 "`end_keywords\n",
                                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  DiagEngine diag2(f.mgr);
  Lexer lexer(preprocessed, 0, diag2);
  auto tokens = lexer.LexAll();
  // Find the token after "reg" — should be kIdentifier ("logic"), not kKwLogic.
  for (size_t i = 0; i + 1 < tokens.size(); ++i) {
    if (tokens[i].kind == TokenKind::kKwReg) {
      EXPECT_EQ(tokens[i + 1].kind, TokenKind::kIdentifier);
      EXPECT_EQ(tokens[i + 1].text, "logic");
      return;
    }
  }
  FAIL() << "did not find 'reg' token in lexed output";
}

TEST(Preprocessor, BeginKeywords_RestoresAfterEnd) {
  PreprocFixture f;
  auto preprocessed = Preprocess("`begin_keywords \"1364-2001\"\n"
                                 "logic\n"
                                 "`end_keywords\n"
                                 "logic\n",
                                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  DiagEngine diag2(f.mgr);
  Lexer lexer(preprocessed, 0, diag2);
  auto tokens = lexer.LexAll();
  // First "logic" should be identifier (under 1364-2001).
  // Second "logic" should be keyword (restored to 1800-2023).
  ASSERT_GE(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "logic");
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwLogic);
}
