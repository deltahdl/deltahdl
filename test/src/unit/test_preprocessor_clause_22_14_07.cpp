#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywords1800_2009_EmitsCorrectMarker) {
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
}

TEST(KeywordVersionPreprocessing, BeginKeywords1800_2009_CheckerIsKeyword) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2009\"\n"
      "checker\n"
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
    if (tok.text == "checker") {
      EXPECT_EQ(tok.kind, TokenKind::kKwChecker);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(KeywordVersionPreprocessing,
     BeginKeywords1800_2009_InterconnectIsIdentifier) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2009\"\n"
      "interconnect\n"
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
    if (tok.text == "interconnect") {
      EXPECT_EQ(tok.kind, TokenKind::kIdentifier);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
