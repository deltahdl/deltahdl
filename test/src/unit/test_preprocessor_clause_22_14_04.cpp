#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing,
     BeginKeywords1364_2001Noconfig_EmitsCorrectMarker) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001-noconfig\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer13642001Noconfig);
}

TEST(KeywordVersionPreprocessing,
     BeginKeywords1364_2001Noconfig_ConfigIsIdentifier) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001-noconfig\"\n"
      "config\n"
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
    if (tok.text == "config") {
      EXPECT_EQ(tok.kind, TokenKind::kIdentifier);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(KeywordVersionPreprocessing,
     BeginKeywords1364_2001Noconfig_GenerateIsKeyword) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001-noconfig\"\n"
      "generate\n"
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
    if (tok.text == "generate") {
      EXPECT_EQ(tok.kind, TokenKind::kKwGenerate);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
