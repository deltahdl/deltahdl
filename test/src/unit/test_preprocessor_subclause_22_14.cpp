#include <gtest/gtest.h>
#include <unistd.h>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

namespace fs = std::filesystem;

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unrecognized version specifier: \"9999-9999\"", 1,
                            "22.14"));
}

TEST(KeywordVersionPreprocessing, ErrorMissingQuotedString) {
  PreprocFixture f;
  Preprocess("`begin_keywords\n`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "expected quoted version string after `begin_keywords", 1, "22.14"));
}

TEST(KeywordVersionPreprocessing, ErrorMissingClosingQuote) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"1800-2023\n`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "expected quoted version string after `begin_keywords", 1, "22.14"));
}

TEST(KeywordVersionPreprocessing, ErrorEndKeywordsWithoutBegin) {
  PreprocFixture f;
  Preprocess("`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`end_keywords without matching `begin_keywords", 1,
                            "22.14"));
}

TEST(KeywordVersionPreprocessing, ErrorEndKeywordsWithoutBeginNames22_14) {
  PreprocFixture f;
  Preprocess("`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`end_keywords without matching `begin_keywords", 1,
                            "22.14"));
}

TEST(KeywordVersionPreprocessing, ErrorEmptyVersionString) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"\"\n`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unrecognized version specifier: \"\"", 1,
                            "22.14"));
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
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
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
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
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
  Lexer lexer(mgr.FileContent(out_fid), out_fid, diag,
              TextOrigin::kPreprocessorOutput);
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

std::vector<TokenKind> KindsOf(const std::string& preprocessed,
                               std::string_view text) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", preprocessed);
  Lexer lexer(mgr.FileContent(fid), fid, diag, TextOrigin::kPreprocessorOutput);
  std::vector<TokenKind> kinds;
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == text) kinds.push_back(tok.kind);
  }
  return kinds;
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`begin_keywords without matching `end_keywords", 1,
                            "22.14"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`begin_keywords without matching `end_keywords", 1,
                            "22.14"));
}

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

TEST(KeywordVersionPreprocessing, KeywordRegionSpansSeparateSourceFiles) {
  PreprocFixture f;
  auto first = f.mgr.AddFile("<first>", "`begin_keywords \"1364-2001\"\n");
  auto second = f.mgr.AddFile("<second>", "logic\n`end_keywords\n");

  Preprocessor pp(f.mgr, f.diag, {});
  std::string out = pp.Preprocess(first);
  out += pp.Preprocess(second);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());

  auto kinds = KindsOf(out, "logic");
  ASSERT_EQ(kinds.size(), 1u);
  EXPECT_EQ(kinds[0], TokenKind::kIdentifier);
}

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
  EXPECT_NE(out.find('7'), std::string::npos);
  EXPECT_EQ(out.find(kKeywordMarker), std::string::npos);
}

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

TEST(KeywordVersionPreprocessing, ErrorUnquotedVersionSpecifier) {
  PreprocFixture f;
  Preprocess("`begin_keywords 1800-2023\n`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "expected quoted version string after `begin_keywords", 1, "22.14"));
}

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

TEST(KeywordVersionPreprocessing, ErrorPaddedVersionSpecifier) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"  1800-2023  \"\n`end_keywords\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unrecognized version specifier: \"  1800-2023  \"",
                            1, "22.14"));
}

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

  EXPECT_EQ(KindsOf(out, "wire").size(), 2u);
  EXPECT_EQ(KindsOf(out, "second").size(), 1u);
}

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
    EXPECT_TRUE(ReportedError(begin_fixture.diag.Diagnostics(),
                              "`begin_keywords illegal inside a design element",
                              2, "22.14"))
        << c.header;

    PreprocFixture end_fixture;
    Preprocess("`begin_keywords \"1800-2023\"\n" + std::string(c.header) +
                   "\n`end_keywords\n" + c.footer + "\n",
               end_fixture);
    EXPECT_TRUE(ReportedError(end_fixture.diag.Diagnostics(),
                              "`end_keywords illegal inside a design element",
                              3, "22.14"))
        << c.header;
  }
}

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

TEST(KeywordVersionPreprocessing, LegalAfterInterfaceClassNamedOnTheNextLine) {
  PreprocFixture f;
  Preprocess(
      "interface class\n"
      "IC;\n"
      "endclass\n"
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(KeywordVersionPreprocessing, ErrorInsideInterfaceNamedLikeClass) {
  PreprocFixture f;
  Preprocess(
      "interface classy_if;\n"
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n"
      "endinterface\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`begin_keywords illegal inside a design element",
                            2, "22.14"));
}

TEST(KeywordVersionPreprocessing, ErrorInsideTabSeparatedDesignElementHeader) {
  PreprocFixture f;
  Preprocess(
      "module\tm;\n"
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`begin_keywords illegal inside a design element",
                            2, "22.14"));
}

TEST(KeywordVersionPreprocessing, PlacementOnSharedLineFollowsTheElement) {
  PreprocFixture inside;
  Preprocess("module m; `begin_keywords \"1364-2001\"\n`end_keywords\n",
             inside);
  EXPECT_TRUE(ReportedError(inside.diag.Diagnostics(),
                            "`begin_keywords illegal inside a design element",
                            1, "22.14"));

  PreprocFixture outside;
  Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "module m;\n"
      "endmodule `end_keywords\n",
      outside);
  EXPECT_FALSE(outside.diag.HasErrors());
}

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

TEST(KeywordVersionPreprocessing, VersionDoesNotChangeOtherTokens) {
  const std::string kBody = "a = 12'h1F + 3.5e-2; b = \"txt\"; c <= d ** 2;\n";

  PreprocFixture guarded;
  auto with_region = Preprocess(
      "`begin_keywords \"1364-1995\"\n" + kBody + "`end_keywords\n", guarded);
  EXPECT_FALSE(guarded.diag.HasErrors());

  PreprocFixture plain;
  auto without_region = Preprocess(kBody, plain);
  EXPECT_FALSE(plain.diag.HasErrors());

  auto kinds = [](const std::string& src) {
    SourceManager mgr;
    DiagEngine diag(mgr);
    auto fid = mgr.AddFile("<test>", src);
    Lexer lexer(mgr.FileContent(fid), fid, diag,
                TextOrigin::kPreprocessorOutput);
    std::vector<std::pair<TokenKind, std::string>> out;
    for (const auto& tok : lexer.LexAll()) {
      out.emplace_back(tok.kind, std::string(tok.text));
    }
    return out;
  };
  EXPECT_EQ(kinds(with_region), kinds(without_region));
}

TEST(KeywordVersionPreprocessing, CommentAheadOfTheDirectiveKeepsItsText) {
  PreprocFixture f;
  auto out = Preprocess(
      "/* region */ `begin_keywords \"1800-2023\"\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  std::string marked = "/* region */ ";
  marked += kKeywordMarker;
  marked += static_cast<char>(KeywordVersion::kVer18002023);
  EXPECT_NE(out.find(marked), std::string::npos);
}

}  // namespace
