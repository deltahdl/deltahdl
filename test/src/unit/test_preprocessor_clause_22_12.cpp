#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>

#include "fixture_preprocessor.h"

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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingFilename) {
  PreprocFixture f;
  Preprocess("`line 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingAll) {
  PreprocFixture f;
  Preprocess("`line\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_ZeroLineNumber_Error) {
  PreprocFixture f;
  Preprocess("`line 0 \"test.sv\" 0\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NegativeLineNumber) {
  PreprocFixture f;
  Preprocess("`line -12 \"somefile\" 0\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NonStringFilename) {
  PreprocFixture f;
  Preprocess("`line 1 somefile 2\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_UnterminatedFilename) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile 0\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_TrailingContent_Error) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0 wire x;\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_TrailingComment_Error) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0 // comment\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_TrailingBlockComment_Error) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0 /* comment */\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
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
