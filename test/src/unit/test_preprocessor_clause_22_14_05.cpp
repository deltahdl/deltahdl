#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2005_EmitsCorrectMarker) {
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
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2005_UwireIsKeyword) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
      "uwire\n"
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
    if (tok.text == "uwire") {
      EXPECT_EQ(tok.kind, TokenKind::kKwUwire);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(KeywordVersionPreprocessing, BeginKeywords1364_2005_LogicIsIdentifier) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2005\"\n"
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

}  // namespace
