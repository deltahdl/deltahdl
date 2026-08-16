#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

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

// §5.2 makes a source file a stream of lexical tokens and lists the seven kinds
// there are; kKeywordMarker, the byte 0x01, begins none of them, so a source
// holding one is rejected at the character it stands on.
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

// What that report protects. The Preprocessor writes kKeywordMarker itself to
// introduce a keyword-version change, and Lexer reads the byte after every
// marker it finds as a KeywordVersion, so a 0x01 the user wrote that survived
// into the output would set the reserved word list to whatever byte followed
// it instead of being diagnosed.
TEST(LexicalConventionPreprocessor,
     KeywordMarkerByteIsBlankedFromPreprocessedText) {
  PreprocFixture f;
  auto out = Preprocess(
      "module t;\n"
      "  logic \x01 a;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
}

// A value given for a macro on the command line is text of the same kind, and
// §5.2 lists no token a 0x01 byte begins wherever it stands. The value never
// passes through the scan the source text above meets, so the report is the
// only thing that says the byte was read at all. A command-line define stands
// on no line of any file, which is the line 0 below.
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

// What that report protects, in the text the macro's expansion writes. The
// source expands `WIDTH, so the value reaches the output rather than sitting in
// the macro table where no assertion about the output could fail.
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
}

// Lexes `src` and returns the kind of the first token whose spelling is
// `word`, or kError when the token never appears.
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

// The consequence a surviving marker has, which neither assertion above shows:
// Lexer::ConsumeKeywordMarker reads the byte after a marker as a
// KeywordVersion, so a value carrying a marker and a version byte would select
// a reserved word list for every token the expansion precedes. §22.14 gives
// `begin_keywords as the only thing that selects one. `logic` separates the two
// lists that byte would choose between: §22.14.6 reserves it from IEEE Std
// 1800-2005 and the IEEE Std 1364-1995 list of §22.14.2 omits it, so it lexes
// as an identifier when the value took effect and as its keyword when it did
// not.
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
}

}  // namespace
