#include <gtest/gtest.h>

#include <cstdio>
#include <filesystem>
#include <fstream>
#include <string>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "fixture_preprocessor.h"
#include "helpers_include_test_dir.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, Line_OverridesLineNumber) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 42 \"foo.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasLineOverride());
  EXPECT_EQ(pp.LineOffset(), 42u);
}

TEST(Preprocessor, Line_OverridesFileName) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 10 \"original.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineFile(), "original.sv");
}

TEST(Preprocessor, Line_FullPathFilename) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 1 \"/home/user/src/design.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineFile(), "/home/user/src/design.sv");
}

TEST(Preprocessor, Line_RelativePathFilename) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 5 \"../lib/pkg.sv\" 1\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineFile(), "../lib/pkg.sv");
}

TEST(Preprocessor, Line_Level0_NoError) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_Level1_IncludeEnter) {
  PreprocFixture f;
  Preprocess("`line 1 \"included.sv\" 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_Level2_IncludeExit) {
  PreprocFixture f;
  Preprocess("`line 3 \"orig.v\" 2\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_IllegalLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\" 3\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line level must be 0, 1, or 2", 1, "22.12"));
}

TEST(Preprocessor, Line_MissingFilename) {
  PreprocFixture f;
  Preprocess("`line 1\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line directive requires a quoted filename", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_MissingLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line directive requires a level (0, 1, or 2)", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_LevelThatIsNoNumber) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\" x\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line directive requires a level (0, 1, or 2)", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_MissingAll) {
  PreprocFixture f;
  Preprocess("`line\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "invalid `line directive: missing or invalid line number", 1, "22.12"));
}

TEST(Preprocessor, Line_ZeroLineNumber_Error) {
  PreprocFixture f;
  Preprocess("`line 0 \"test.sv\" 0\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line number must be a positive integer", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_NonPositiveNumberNames22_12) {
  PreprocFixture f;
  Preprocess("`line 0 \"f\" 0\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line number must be a positive integer", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_NegativeLineNumber) {
  PreprocFixture f;
  Preprocess("`line -12 \"somefile\" 0\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "invalid `line directive: missing or invalid line number", 1, "22.12"));
}

TEST(Preprocessor, Line_NonStringFilename) {
  PreprocFixture f;
  Preprocess("`line 1 somefile 2\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`line directive requires a quoted filename", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_UnterminatedFilename) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile 0\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unterminated string in `line directive", 1,
                            "22.12"));
}

TEST(Preprocessor, Line_TrailingContent_Error) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0 wire x;\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only whitespace may appear on the same line as `line", 1, "22.12"));
}

TEST(Preprocessor, Line_TrailingComment_Error) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0 // comment\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only whitespace may appear on the same line as `line", 1, "22.12"));
}

TEST(Preprocessor, Line_TrailingBlockComment_Error) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0 /* comment */\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only whitespace may appear on the same line as `line", 1, "22.12"));
}

TEST(Preprocessor, Line_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`line 10 \"foo.sv\" 0\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Line_ResetallDoesNotAffect) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 42 \"override.sv\" 0\n", f, pp);
  EXPECT_TRUE(pp.HasLineOverride());
  EXPECT_EQ(pp.LineOffset(), 42u);
  EXPECT_EQ(pp.LineFile(), "override.sv");
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_TRUE(pp.HasLineOverride());
  EXPECT_EQ(pp.LineOffset(), 42u);
  EXPECT_EQ(pp.LineFile(), "override.sv");
}

TEST(Preprocessor, Line_AffectsUnderscoreLineMacro) {
  PreprocFixture f;
  auto out = Preprocess("`line 100 \"test.sv\" 0\n`__LINE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("100"), std::string::npos);
}

TEST(Preprocessor, Line_AffectsUnderscoreFileMacro) {
  PreprocFixture f;
  auto out = Preprocess("`line 1 \"overridden.sv\" 0\n`__FILE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("overridden.sv"), std::string::npos);
}

TEST(Preprocessor, Line_InsideModule_NoError) {
  PreprocFixture f;
  Preprocess("module m;\n`line 5 \"inner.sv\" 0\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_InsideIfdef_Active) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`define HAS_LINE\n`ifdef HAS_LINE\n`line 99 \"cond.sv\" 0\n`endif\n", f,
      pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasLineOverride());
  EXPECT_EQ(pp.LineOffset(), 99u);
}

TEST(Preprocessor, Line_InsideIfdef_Inactive) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`ifdef UNDEF_FLAG\n`line 99 \"cond.sv\" 0\n`endif\n", f,
                   pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.HasLineOverride());
}

TEST(Preprocessor, Line_MultipleOverrides_LastWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 10 \"first.sv\" 0\n`line 20 \"second.sv\" 0\n", f,
                   pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineOffset(), 20u);
  EXPECT_EQ(pp.LineFile(), "second.sv");
}

TEST(Preprocessor, Line_LargeLineNumber) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 999999 \"big.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineOffset(), 999999u);
}

TEST(Preprocessor, Line_TrailingWhitespaceAfterLevel_NoError) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0   \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_BetweenModules_NoInterference) {
  PreprocFixture f;
  auto out = Preprocess(
      "module m1;\nendmodule\n"
      "`line 50 \"mid.sv\" 0\n"
      "module m2;\nendmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("module m1;"), std::string::npos);
  EXPECT_NE(out.find("module m2;"), std::string::npos);
}

TEST(Preprocessor, Line_IncrementAcrossMultipleLines) {
  PreprocFixture f;
  auto out = Preprocess(
      "`line 10 \"f.sv\" 0\n"
      "first\n"
      "second\n"
      "`__LINE__\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("12"), std::string::npos);
}

TEST(Preprocessor, Line_FileOverridePersistsAcrossLines) {
  PreprocFixture f;
  auto out = Preprocess(
      "`line 1 \"persistent.sv\" 0\n"
      "wire a;\n"
      "wire b;\n"
      "`__FILE__\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("persistent.sv"), std::string::npos);
}

TEST(Preprocessor, Line_NaturalCountingStartsAtOne) {
  PreprocFixture f;
  auto out = Preprocess("`__LINE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find('1'), std::string::npos);
}

TEST(Preprocessor, Line_NaturalCountingIncrements) {
  PreprocFixture f;
  auto out = Preprocess("a\nb\n`__LINE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find('3'), std::string::npos);
}

TEST(Preprocessor, Line_IncludeSavesAndRestores) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_12_save";
  std::string inc_path = tmp_dir + "/stub.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "// included\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess(
      "`__LINE__\n"
      "`include \"stub.svh\"\n"
      "`__LINE__\n",
      f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('1'), std::string::npos);
  EXPECT_NE(result.find('3'), std::string::npos);

  std::remove(inc_path.c_str());
  std::filesystem::remove_all(tmp_dir);
}

TEST(Preprocessor, Line_IncludeFileResetsLineCountToOne) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_12_reset";
  std::string inc_path = tmp_dir + "/counted.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "// pad a\n// pad b\n`__LINE__\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess(
      "wire a;\n"
      "`include \"counted.svh\"\n",
      f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('3'), std::string::npos);
  EXPECT_EQ(result.find('4'), std::string::npos);

  std::remove(inc_path.c_str());
  std::filesystem::remove_all(tmp_dir);
}

TEST(Preprocessor, Line_LibrarySearchUnaffectedByOverride) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_12_lib";
  std::string inc_path = tmp_dir + "/real.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "wire from_real_file;\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess(
      "`line 100 \"phantom_path_that_does_not_exist.sv\" 0\n"
      "`include \"real.svh\"\n",
      f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("from_real_file"), std::string::npos);

  std::remove(inc_path.c_str());
  std::filesystem::remove_all(tmp_dir);
}

static void PreprocessAndParseUnder(const std::string& path,
                                    const std::string& src, PreprocFixture& f,
                                    Arena& arena, PreprocConfig cfg = {}) {
  auto fid = f.mgr.AddFile(path, src);
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto out = pp.Preprocess(fid);
  auto out_fid =
      f.mgr.AddPreprocessedFile("<preprocessed>", out, pp.LineOrigins());
  Lexer lexer(f.mgr.FileContent(out_fid), out_fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, arena, f.diag);
  parser.Parse();
}

static std::string FirstErrorLocation(PreprocFixture& f) {
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError) return f.mgr.FormatLoc(d.loc);
  }
  return "<no error was reported>";
}

TEST(Preprocessor, ReportAfterPreprocessingNamesTheFileItWasWrittenIn) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("design.sv",
                          "module m;\n"
                          "endmodule\n"
                          "%\n",
                          f, arena);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 3, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "design.sv:3:1");
}

TEST(Preprocessor, ReportBelowAnIncludeStandsAtTheIncludingFilesOwnLine) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_12_origin";
  std::string inc_path = tmp_dir + "/pad.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "// pad a\n// pad b\n// pad c\n";
  }

  PreprocFixture f;
  Arena arena;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  PreprocessAndParseUnder("top.sv",
                          "`include \"pad.svh\"\n"
                          "module m;\n"
                          "endmodule\n"
                          "%\n",
                          f, arena, cfg);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 7, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "top.sv:4:1");

  std::remove(inc_path.c_str());
  std::filesystem::remove_all(tmp_dir);
}

TEST(Preprocessor, ReportBelowALineDirectiveTakesTheNameAndNumberItSet) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("generated.sv",
                          "`line 3 \"orig.v\" 2\n"
                          "%\n",
                          f, arena);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 2, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "orig.v:3:1");
}

TEST(Preprocessor, ReportBelowAMultiLineExpansionStandsAtItsOwnLine) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("design.sv",
                          "`define TWO module m; \\\n"
                          "endmodule\n"
                          "`TWO\n"
                          "%\n",
                          f, arena);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 4, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "design.sv:4:1");
}

TEST(Preprocessor, ReportInsideAMultiLineExpansionStandsAtTheLineOfTheUse) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("design.sv",
                          "`define BAD module m; \\\n"
                          "endmodule \\\n"
                          "%\n"
                          "`BAD\n",
                          f, arena);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 4, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "design.sv:4:1");
}

TEST(Preprocessor, ReportBelowALineDirectiveNamingTheEmptyName) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("generated.sv",
                          "`line 5 \"\" 0\n"
                          "%\n",
                          f, arena);
  EXPECT_EQ(FirstErrorLocation(f), ":5:1");
}

static std::string WithIncludeDir(const std::string& src,
                                  const IncludeTestDir& dir,
                                  PreprocFixture& f) {
  PreprocConfig cfg;
  cfg.include_dirs.push_back(dir.dir.string());
  return Preprocess(src, f, cfg);
}

TEST(Preprocessor, Line_InsideAnIncludedFileRenamesTheRestOfThatFile) {
  IncludeTestDir dir;
  dir.WriteFile("named.svh",
                "`line 50 \"fake.svh\" 0\n"
                "inner `__FILE__ `__LINE__\n");
  PreprocFixture f;
  auto out = WithIncludeDir("`include \"named.svh\"\n", dir, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("inner \"fake.svh\" 50"), std::string::npos) << out;
}

TEST(Preprocessor, Line_RestoredAfterAnIncludeWhenSetBeforeIt) {
  IncludeTestDir dir;
  dir.WriteFile("plain.svh", "// plain\n");
  PreprocFixture f;
  auto out = WithIncludeDir(
      "`line 100 \"over.v\" 0\n"
      "`include \"plain.svh\"\n"
      "after `__FILE__ `__LINE__\n",
      dir, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("after \"over.v\" 101"), std::string::npos) << out;
}

TEST(Preprocessor, Line_NestedIncludeRestoresTheOuterIncludedFile) {
  IncludeTestDir dir;
  dir.WriteFile("b.svh", "// inner\n");
  auto outer = dir.WriteFile("a.svh",
                             "// outer\n"
                             "`include \"b.svh\"\n"
                             "outer `__FILE__ `__LINE__\n");
  PreprocFixture f;
  auto out = WithIncludeDir("`include \"a.svh\"\n", dir, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("outer \"" + outer.string() + "\" 3"), std::string::npos)
      << out;
}

TEST(Preprocessor, DISABLED_Line_SetInsideAnIncludeIsUndoneWhenTheIncludeEnds) {
  IncludeTestDir dir;
  dir.WriteFile("sets.svh",
                "`line 70 \"inner.svh\" 0\n"
                "// body\n");
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, [&] {
    PreprocConfig cfg;
    cfg.include_dirs.push_back(dir.dir.string());
    return cfg;
  }());
  auto fid = f.mgr.AddFile("top.sv",
                           "`include \"sets.svh\"\n"
                           "after `__FILE__ `__LINE__\n");
  auto out = pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("after \"top.sv\" 2"), std::string::npos) << out;
}

TEST(Preprocessor, DISABLED_Line_AnIncludedFileTakesItsOwnNameAndLineOne) {
  IncludeTestDir dir;
  auto inc = dir.WriteFile("own.svh", "inside `__FILE__ `__LINE__\n");
  PreprocFixture f;
  auto out = WithIncludeDir(
      "`line 300 \"over.sv\" 0\n"
      "`include \"own.svh\"\n",
      dir, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("inside \"" + inc.string() + "\" 1"), std::string::npos)
      << out;
}

TEST(Preprocessor, DISABLED_Line_ASecondSourceFileTakesItsOwnNameAndLineOne) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(f.mgr.AddFile("first.sv", "`line 300 \"over.sv\" 0\n"));
  auto out =
      pp.Preprocess(f.mgr.AddFile("second.sv", "second `__FILE__ `__LINE__\n"));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("second \"second.sv\" 1"), std::string::npos) << out;
}

TEST(Preprocessor, DISABLED_Line_ARealOrBasedNumberIsRejected) {
  for (const char* number : {"1.5", "8'd5"}) {
    PreprocFixture f;
    Preprocess(std::string("`line ") + number + " \"f.sv\" 0\n", f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "invalid `line directive: missing or invalid line number", 1, "22.12"))
        << number;
  }
}

TEST(Preprocessor, DISABLED_Line_ANumberPast32BitsIsNotWrapped) {
  for (const char* number : {"4294967297", "99999999999999999999"}) {
    PreprocFixture f;
    auto out = Preprocess(
        std::string("`line ") + number + " \"f.sv\" 0\n`__LINE__\n", f);
    bool reported = f.diag.HasErrors();
    EXPECT_TRUE(reported || out.find(number) != std::string::npos)
        << number << " gave " << out;
  }
}

TEST(Preprocessor, DISABLED_Line_CodeBeforeTheDirectiveIsRejected) {
  for (const char* before : {"wire x; ", "/* c */ "}) {
    PreprocFixture f;
    Preprocess(
        std::string("module t;\n") + before + "`line 1 \"f.v\" 0\nendmodule\n",
        f);
    bool reported = false;
    for (const auto& d : f.diag.Diagnostics()) {
      reported = reported || (d.severity == DiagSeverity::kError &&
                              d.loc.line == 2 && d.subclause == "22.12");
    }
    EXPECT_TRUE(reported) << before;
  }
}

TEST(Preprocessor, Line_CommentsOnTheLinesAroundTheDirectiveAreAccepted) {
  PreprocFixture f;
  auto out = Preprocess(
      "// above\n"
      "`line 20 \"f.v\" 0\n"
      "// below\n"
      "at `__LINE__\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("at 21"), std::string::npos) << out;
}

struct LineHost {
  const char* opener;
  const char* closer;
};

TEST(Preprocessor, Line_AcceptedAndAppliedInsideEveryBody) {
  for (const auto& h : {
           LineHost{"package p;\n", "endpackage\n"},
           LineHost{"class k;\n", "endclass\n"},
           LineHost{"module m;\nfunction void f();\n",
                    "endfunction\nendmodule\n"},
           LineHost{"module m;\ntask tk();\n", "endtask\nendmodule\n"},
           LineHost{"interface i;\n", "endinterface\n"},
           LineHost{"program g;\n", "endprogram\n"},
           LineHost{"", ""},
       }) {
    PreprocFixture f;
    auto out = Preprocess(std::string(h.opener) +
                              "`line 77 \"h.v\" 0\n"
                              "localparam int L = `__LINE__;\n" +
                              h.closer,
                          f);
    EXPECT_FALSE(f.diag.HasErrors()) << h.opener;
    EXPECT_NE(out.find("L = 77;"), std::string::npos) << h.opener << out;
  }
}

TEST(Preprocessor, Line_NamingAnotherDirectoryLeavesIncludeSearchAlone) {
  IncludeTestDir dir;
  dir.WriteFile("real/x.svh", "from_the_real_directory\n");
  auto other = dir.WriteFile("other/x.svh", "from_the_named_directory\n");
  const std::string kTopText = "`line 1 \"" +
                               (other.parent_path() / "top.sv").string() +
                               "\" 0\n`include \"x.svh\"\n";
  auto top = dir.WriteFile("real/top.sv", kTopText);
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = pp.Preprocess(f.mgr.AddFile(top.string(), kTopText));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("from_the_real_directory"), std::string::npos) << out;
  EXPECT_EQ(out.find("from_the_named_directory"), std::string::npos) << out;
}
