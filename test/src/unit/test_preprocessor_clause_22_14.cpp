#include <gtest/gtest.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

namespace fs = std::filesystem;

// Scratch directory used to exercise `begin_keywords` spanning an `include
// boundary. Cleans itself up on destruction.
struct KeywordIncludeDir {
  fs::path dir;

  KeywordIncludeDir() {
    dir = fs::temp_directory_path() /
          ("delta_kw_22_14_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~KeywordIncludeDir() { fs::remove_all(dir); }

  fs::path Write(const std::string& name, const std::string& content) {
    auto full = dir / name;
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

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

// §22.14: `resetall does not undo the effect of `begin_keywords. The 1364-2001
// keyword set is selected and then `resetall appears; afterward `logic` (a word
// reserved only in later standards) must still lex as an identifier, directly
// showing the active keyword version survived the reset rather than reverting
// to the default set.
TEST(KeywordVersionPreprocessing, ResetallDoesNotAffectKeywordVersion) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "`resetall\n"
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

// §22.14: a `begin_keywords directive affects all source that follows, even
// across source file boundaries, until the matching `end_keywords. Here the
// directive lives in the top file while the affected `logic` identifier lives
// in an included file; under "1364-2001" it must still lex as an identifier.
TEST(KeywordVersionPreprocessing, EffectCrossesIncludeBoundary) {
  KeywordIncludeDir tmp;
  tmp.Write("inc.svh", "logic\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`begin_keywords \"1364-2001\"\n"
                           "`include \"inc.svh\"\n"
                           "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto out_fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(out_fid), out_fid, diag);
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

// Lexes preprocessed text and returns the kind of every token whose spelling
// matches `text`, so a test can say what a particular word turned into.
std::vector<TokenKind> KindsOf(const std::string& preprocessed,
                               std::string_view text) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", preprocessed);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  std::vector<TokenKind> kinds;
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == text) kinds.push_back(tok.kind);
  }
  return kinds;
}

// §22.14: the two directives shall be used as a pair, `begin_keywords first
// and `end_keywords sometime later. A region that is opened and never closed
// has no matching `end_keywords anywhere, which is only knowable once the last
// source file has been preprocessed.
TEST(KeywordVersionPreprocessing, ErrorBeginKeywordsNeverClosed) {
  PreprocFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`begin_keywords \"1364-2001\"\n"
                           "module m;\n"
                           "endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());

  pp.ReportUnterminatedKeywordRegions();
  EXPECT_TRUE(f.diag.HasErrors());
}

// The inner directive of a nested pair is the one left unmatched here: the
// single `end_keywords closes the inner region, so the outer one is reported.
TEST(KeywordVersionPreprocessing, ErrorNestedBeginKeywordsNeverClosed) {
  PreprocFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`begin_keywords \"1800-2005\"\n"
                           "`begin_keywords \"1364-1995\"\n"
                           "x\n"
                           "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());

  pp.ReportUnterminatedKeywordRegions();
  EXPECT_TRUE(f.diag.HasErrors());
}

// A properly paired region draws no complaint from the same end-of-compilation
// check, which keeps the diagnostic above from being unconditional.
TEST(KeywordVersionPreprocessing, ClosedRegionIsNotReportedUnterminated) {
  PreprocFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`begin_keywords \"1364-2001\"\n"
                           "x\n"
                           "`end_keywords\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
}

// §22.14: a `begin_keywords region affects all source that follows, across
// source file boundaries, until the matching `end_keywords. The pair is split
// across two separately preprocessed files here: the region opened in the
// first file is still in effect at the top of the second, where `logic` lexes
// as an identifier, and the `end_keywords in the second file closes it, so
// nothing is left unterminated.
TEST(KeywordVersionPreprocessing, KeywordRegionSpansSeparateSourceFiles) {
  PreprocFixture f;
  auto first = f.mgr.AddFile("<first>", "`begin_keywords \"1364-2001\"\n");
  auto second = f.mgr.AddFile("<second>", "logic\n`end_keywords\n");

  Preprocessor pp(f.mgr, f.diag, {});
  // The driver preprocesses each source file with the same preprocessor and
  // concatenates the results, which is what lets a region opened in one file
  // still be in effect in the next.
  std::string out = pp.Preprocess(first);
  out += pp.Preprocess(second);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());

  auto kinds = KindsOf(out, "logic");
  ASSERT_EQ(kinds.size(), 1u);
  EXPECT_EQ(kinds[0], TokenKind::kIdentifier);
}

// §22.14 names the closing directive `end_keywords exactly. A macro whose name
// merely starts with those characters is a macro usage, not a directive, so it
// must expand rather than try to close a keyword region that was never opened.
TEST(KeywordVersionPreprocessing, MacroNamedLikeEndKeywordsIsNotTheDirective) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define end_keywords_saved 42\n"
      "`end_keywords_saved\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("42"), std::string::npos);
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
}

// The same whole-word rule for the opening directive: `begin_keywords_note is
// a macro usage, so no version_specifier is demanded and no keyword region is
// opened for the end-of-compilation check to complain about.
TEST(KeywordVersionPreprocessing,
     MacroNamedLikeBeginKeywordsIsNotTheDirective) {
  PreprocFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`define begin_keywords_note 7\n"
                           "`begin_keywords_note\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = pp.Preprocess(fid);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("7"), std::string::npos);
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
}

// The whole-word rule keys off name characters, and a quotation mark is not
// one: Syntax 22-10 puts the version_specifier in quotes, so a quote sitting
// flush against the keyword still ends it and the directive is recognized.
TEST(KeywordVersionPreprocessing, QuoteFlushAgainstBeginKeywordsIsRecognized) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords\"1800-2012\"\n"
      "x\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002012);
}

// Syntax 22-10 requires the version_specifier to be quoted. The bare text of a
// legal specifier is not the directive's operand form.
TEST(KeywordVersionPreprocessing, ErrorUnquotedVersionSpecifier) {
  PreprocFixture f;
  Preprocess("`begin_keywords 1800-2023\n`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A directive need not start in column one. Both halves of the pair are still
// the directive when the line is indented.
TEST(KeywordVersionPreprocessing, IndentedDirectiveIsRecognized) {
  PreprocFixture f;
  auto out = Preprocess(
      "    `begin_keywords \"1364-2001\"\n"
      "logic\n"
      "\t`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto kinds = KindsOf(out, "logic");
  ASSERT_EQ(kinds.size(), 1u);
  EXPECT_EQ(kinds[0], TokenKind::kIdentifier);
}

// Syntax 22-10 ends `begin_keywords at its quoted version_specifier, so a
// comment may follow on the same line without becoming part of the operand.
TEST(KeywordVersionPreprocessing, TrailingCommentAfterDirectiveIsIgnored) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1800-2012\" // pick the 1800-2012 reserved words\n"
      "x\n"
      "`end_keywords // and restore the default set\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = out.find(kKeywordMarker);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_EQ(static_cast<KeywordVersion>(out[pos + 1]),
            KeywordVersion::kVer18002012);
}

// The mirror of the skipped-branch case: a `begin_keywords reached through a
// conditional branch that is taken opens its region normally.
TEST(KeywordVersionPreprocessing, BeginKeywordsInTakenIfdefBranch) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define USE_OLD_KEYWORDS 1\n"
      "`ifdef USE_OLD_KEYWORDS\n"
      "`begin_keywords \"1364-2001\"\n"
      "`endif\n"
      "logic\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto kinds = KindsOf(out, "logic");
  ASSERT_EQ(kinds.size(), 1u);
  EXPECT_EQ(kinds[0], TokenKind::kIdentifier);
}

// Syntax 22-10 lists the version_specifier alternatives as exact text. The
// quotes delimit the operand, so padding inside them is part of the specifier
// and makes it one the production does not list.
TEST(KeywordVersionPreprocessing, ErrorPaddedVersionSpecifier) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"  1800-2023  \"\n`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §22.14: the region runs until the matching `end_keywords wherever that
// directive lives. Here the closing half sits in an included file, so the
// boundary is crossed by the close rather than by the region's body: `logic` is
// an identifier before the include and the type keyword again after it.
TEST(KeywordVersionPreprocessing, EndKeywordsInIncludedFileClosesRegion) {
  KeywordIncludeDir tmp;
  tmp.Write("close.svh", "`end_keywords\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`begin_keywords \"1364-2001\"\n"
                           "logic\n"
                           "`include \"close.svh\"\n"
                           "logic\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = pp.Preprocess(fid);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());

  auto kinds = KindsOf(out, "logic");
  ASSERT_EQ(kinds.size(), 2u);
  EXPECT_EQ(kinds[0], TokenKind::kIdentifier);
  EXPECT_EQ(kinds[1], TokenKind::kKwLogic);
}

// Syntax 22-10 ends `begin_keywords at its quoted version_specifier and
// `end_keywords at the keyword itself, so neither directive claims the rest of
// its line. Source text sharing the line is ordinary source, and it is already
// governed by the version the directive just selected or restored.
TEST(KeywordVersionPreprocessing, SourceOnTheDirectiveLineIsOrdinarySource) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"1364-2001\" wire logic;\n"
      "`end_keywords wire second;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto opened = KindsOf(out, "logic");
  ASSERT_EQ(opened.size(), 1u);
  EXPECT_EQ(opened[0], TokenKind::kIdentifier);

  // Both trailing declarations survived into the output rather than being
  // swallowed by the directive.
  EXPECT_EQ(KindsOf(out, "wire").size(), 2u);
  EXPECT_EQ(KindsOf(out, "second").size(), 1u);
}

// §22.14: both directives can only appear outside a design element. §3.2 lists
// the design element kinds, and the restriction is not specific to modules, so
// each kind is checked in turn with the directive placed inside it.
TEST(KeywordVersionPreprocessing, ErrorInsideEveryDesignElementKind) {
  struct Case {
    const char* header;
    const char* footer;
  };
  const Case kCases[] = {
      {"module m;", "endmodule"},
      {"macromodule m;", "endmodule"},
      {"program p;", "endprogram"},
      {"interface i;", "endinterface"},
      {"checker c;", "endchecker"},
      {"package pkg;", "endpackage"},
      {"primitive prim (o, i);", "endprimitive"},
      {"config cfg;", "endconfig"},
  };
  for (const auto& c : kCases) {
    PreprocFixture begin_fixture;
    Preprocess(std::string(c.header) + "\n`begin_keywords \"1800-2023\"\n" +
                   c.footer + "\n",
               begin_fixture);
    EXPECT_TRUE(begin_fixture.diag.HasErrors()) << c.header;

    PreprocFixture end_fixture;
    Preprocess("`begin_keywords \"1800-2023\"\n" + std::string(c.header) +
                   "\n`end_keywords\n" + c.footer + "\n",
               end_fixture);
    EXPECT_TRUE(end_fixture.diag.HasErrors()) << c.header;
  }
}

// §22.14 defers to §3.2 for what a design element is, and §3.2's list does not
// include an interface class — that is a class, closed by endclass. Code that
// follows one is still outside every design element, so the pair is legal
// there.
TEST(KeywordVersionPreprocessing, LegalAfterInterfaceClass) {
  PreprocFixture f;
  Preprocess(
      "interface class IC;\n"
      "endclass\n"
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Whatever whitespace separates a design element's keyword from its name, the
// header still opens the element, so the placement rule still rejects a
// directive written inside it.
TEST(KeywordVersionPreprocessing, ErrorInsideTabSeparatedDesignElementHeader) {
  PreprocFixture f;
  Preprocess(
      "module\tm;\n"
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A directive that shares its line with a design element header is inside that
// element, and one that follows the closing keyword is outside it again.
TEST(KeywordVersionPreprocessing, PlacementOnSharedLineFollowsTheElement) {
  PreprocFixture inside;
  Preprocess("module m; `begin_keywords \"1364-2001\"\n`end_keywords\n",
             inside);
  EXPECT_TRUE(inside.diag.HasErrors());

  PreprocFixture outside;
  Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "module m;\n"
      "endmodule `end_keywords\n",
      outside);
  EXPECT_FALSE(outside.diag.HasErrors());
}

// The companion positive: outside every design element is exactly where the
// pair belongs, including in the gap between two of them.
TEST(KeywordVersionPreprocessing, LegalBetweenDesignElements) {
  PreprocFixture f;
  auto out = Preprocess(
      "module a;\n"
      "endmodule\n"
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n"
      "package pkg;\n"
      "endpackage\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find(kKeywordMarker), std::string::npos);
}

// §22.14: the directives only select which identifiers are reserved words.
// They do not change the tokens the source lexes into otherwise, so numbers,
// string literals, operators, and ordinary identifiers come out of an old
// keyword region exactly as they do with no directive at all.
TEST(KeywordVersionPreprocessing, VersionDoesNotChangeOtherTokens) {
  const std::string body = "a = 12'h1F + 3.5e-2; b = \"txt\"; c <= d ** 2;\n";

  PreprocFixture guarded;
  auto with_region = Preprocess(
      "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n", guarded);
  EXPECT_FALSE(guarded.diag.HasErrors());

  PreprocFixture plain;
  auto without_region = Preprocess(body, plain);
  EXPECT_FALSE(plain.diag.HasErrors());

  auto kinds = [](const std::string& src) {
    SourceManager mgr;
    DiagEngine diag(mgr);
    auto fid = mgr.AddFile("<test>", src);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    std::vector<std::pair<TokenKind, std::string>> out;
    for (const auto& tok : lexer.LexAll()) {
      out.emplace_back(tok.kind, std::string(tok.text));
    }
    return out;
  };
  EXPECT_EQ(kinds(with_region), kinds(without_region));
}

}  // namespace
