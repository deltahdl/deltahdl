#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

TEST(LexicalConventionPreprocessor, FreeFormatPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto compact = Preprocess("module t;logic a;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(compact.find("module"), std::string::npos);
  EXPECT_NE(compact.find("endmodule"), std::string::npos);
}

TEST(LexicalConventionPreprocessor, FreeFormatMultilinePreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module\n"
      "  t\n"
      ";\n"
      "  logic\n"
      "    a\n"
      ";\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST(LexicalConventionPreprocessor, MacroExpansionPreservesFreeFormat) {
  PreprocFixture f;
  Preprocess(
      "`define WIDTH 8\n"
      "module t;logic [`WIDTH-1:0] a;endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  PreprocFixture f2;
  Preprocess(
      "`define WIDTH 8\n"
      "module\n  t\n;\n  logic\n  [`WIDTH-1:0]\n  a\n;\nendmodule\n",
      f2);
  EXPECT_FALSE(f2.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, BlockCommentPreservedThroughPreprocessing) {
  PreprocFixture f;
  Preprocess("module/**/t;endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, AllTokenCategoriesPassThroughPreprocessor) {
  PreprocFixture f;
  Preprocess(
      "module t; // line comment\n"
      "  /* block comment */\n"
      "  logic [7:0] data = 8'hAB;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, TabsAndFormfeedsAsWhitespace) {
  PreprocFixture f;
  Preprocess("module\tt\f;\flogic\ta\t;\tendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LexicalConventionPreprocessor, KeywordMarkerByteInSourceTextIsReported) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic \x01 a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unexpected character 0x01 in source text", 2,
                            "5.2"));
}

TEST(LexicalConventionPreprocessor,
     KeywordMarkerByteIsBlankedFromPreprocessedText) {
  PreprocFixture f;
  auto out = Preprocess(
      "module t;\n"
      "  logic \x01 a;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unexpected character 0x01 in source text", 2,
                            "5.2"));
}

TEST(LexicalConventionPreprocessor,
     KeywordMarkerByteInCommandLineDefineValueIsReported) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"WIDTH", std::string("8") + kKeywordMarker}};
  Preprocess(
      "module t;\n"
      "  parameter W = `WIDTH;\n"
      "  logic [W-1:0] a;\n"
      "endmodule\n",
      f, std::move(cfg));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unexpected character 0x01 in the value of command-line define 'WIDTH'",
      0, "5.2"));
}

TEST(LexicalConventionPreprocessor,
     KeywordMarkerByteIsBlankedFromExpandedCommandLineDefine) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"WIDTH", std::string("8") + kKeywordMarker}};
  auto out = Preprocess(
      "module t;\n"
      "  parameter W = `WIDTH;\n"
      "  logic [W-1:0] a;\n"
      "endmodule\n",
      f, std::move(cfg));
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unexpected character 0x01 in the value of command-line define 'WIDTH'",
      0, "5.2"));
}

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

TEST(LexicalConventionPreprocessor,
     CommandLineDefineValueCannotSelectTheReservedWordList) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"WIDTH", std::string("8") + kKeywordMarker +
                               static_cast<char>(static_cast<uint8_t>(
                                   KeywordVersion::kVer13641995))}};
  auto out = Preprocess(
      "module t;\n"
      "  parameter W = `WIDTH;\n"
      "  logic [W-1:0] a;\n"
      "endmodule\n",
      f, std::move(cfg));
  EXPECT_EQ(KindOfWordIn(out, "logic"), TokenKind::kKwLogic);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unexpected character 0x01 in the value of command-line define 'WIDTH'",
      0, "5.2"));
}

TEST(LexicalTokenPreprocessor, BlockCommentInMacroTextSeparatesTokens) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M a/**/b\n"
      "x `M y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out.find("ab"), std::string::npos);
  EXPECT_NE(out.find("a b"), std::string::npos);
}

}  // namespace
