#include <gtest/gtest.h>

#include <cstdio>
#include <filesystem>
#include <fstream>

#include "common/arena.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

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

// §22.12 is what requires the number to be a positive integer, so the record
// the rejection leaves names that subclause. `line carries several rules and
// one report per rule, and the clause is what tells them apart in the record.
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
  // §22.12 requires the line counter to be reset to 1 at the beginning of each
  // file, and an included file is a new file. The `include sits on line 2 of
  // the parent, but `__LINE__ on the third line of the included file must
  // report that file's own line 3 - a counter that continued from the parent
  // would instead yield 4. Observing the reset from inside the include
  // complements Line_IncludeSavesAndRestores, which only observes the parent
  // resuming afterward.
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

// §22.12's first sentence is what the three cases below are about: "The
// compiler shall maintain the current line number and file name of the file
// being compiled." The preprocessor's output is not that file. It splices in
// the lines of every `include and joins a `define body that spanned
// continuation lines, so a position in it names neither the file somebody
// wrote nor the line they wrote it on, and a user handed one is sent to a
// buffer they have never seen.
//
// What answers for the rule is SourceManager::FormatLoc, because that is what
// DiagEngine::Emit in src/common/diagnostic.cpp prints. The report's own
// SourceLoc still stands in the preprocessed text and every other assertion in
// this tree still reads it as such; only what a position is printed as
// changes.

// Preprocesses `src` registered under `path`, registers the output with the
// origins the preprocessor recorded, and parses it -- the sequence
// PreprocessSources and ParseSource in src/main.cpp run. The parse is what
// provokes a report from a stage below the preprocessor, which is the half of
// a run that had no file name of its own.
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

// Where the first error of the run is printed, formatted as
// DiagEngine::Emit in src/common/diagnostic.cpp formats it.
static std::string FirstErrorLocation(PreprocFixture& f) {
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError) return f.mgr.FormatLoc(d.loc);
  }
  return "<no error was reported>";
}

// The file name, on a source with no directive at all. Nothing here moves a
// line, so the line was already right and the name is the whole of the claim:
// every report made after preprocessing named <preprocessed>, which opens no
// file.
TEST(Preprocessor, ReportAfterPreprocessingNamesTheFileItWasWrittenIn) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("design.sv",
                          "module m;\n"
                          "endmodule\n"
                          "%\n",
                          f, arena);

  // The third line opens no top-level declaration, so Parser::ParseTopLevel
  // in src/parser/parser.cpp reports it, standing at its first column.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 3, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "design.sv:3:1");
}

// The line, below an `include. §22.12 requires the current line and file name
// to be stored when an included file is entered and restored when it ends, and
// the included file's lines are spliced into the output where the directive
// stood. The offending line is the fourth of top.sv and the seventh of the
// output, so a run that reports 7 reports a line the user's file does not have.
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

  // Three lines of pad.svh and the directive's own line stand above the module,
  // so the report is at line 7 of the preprocessed text.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 7, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "top.sv:4:1");

  std::remove(inc_path.c_str());
  std::filesystem::remove_all(tmp_dir);
}

// Both halves together, set by the directive §22.12 defines. `line gives the
// following line a number and a file name, and until now it gave them to
// `__FILE__ and `__LINE__ alone while every report ignored it. The file named
// is one this run was never handed, which is why it is registered with no
// content: the report can say where the line came from, and there is no text
// of it to quote back.
TEST(Preprocessor, ReportBelowALineDirectiveTakesTheNameAndNumberItSet) {
  PreprocFixture f;
  Arena arena;
  PreprocessAndParseUnder("generated.sv",
                          "`line 3 \"orig.v\" 2\n"
                          "%\n",
                          f, arena);

  // The directive leaves its own line in the output, so the report stands at
  // line 2 of the preprocessed text whatever name that line is given.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expected top-level declaration", 2, "3.12.1"));
  EXPECT_EQ(FirstErrorLocation(f), "orig.v:3:1");
}
