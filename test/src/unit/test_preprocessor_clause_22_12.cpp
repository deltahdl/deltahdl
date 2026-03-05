#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

// --- §22.12: Basic `line directive sets line number and file ---

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

// --- §22.12: Level parameter values ---

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

// --- §22.12: All parameters required ---

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

// --- §22.12: Number must be positive integer ---

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

// --- §22.12: Filename must be a string literal ---

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

// --- §22.12: Only whitespace may appear on the same line ---

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

// --- §22.12: Directive produces no output ---

TEST(Preprocessor, Line_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`line 10 \"foo.sv\" 0\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

// --- §22.12: Surrounding code preserved ---

TEST(Preprocessor, Line_SurroundingCodePreserved) {
  PreprocFixture f;
  auto out = Preprocess("wire a;\n`line 5 \"f.sv\" 0\nwire b;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
}

// --- §22.12: `resetall does NOT affect `line ---

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

// --- §22.12: `line affects `__LINE__ ---

TEST(Preprocessor, Line_AffectsUnderscoreLineMacro) {
  PreprocFixture f;
  auto out = Preprocess("`line 100 \"test.sv\" 0\n`__LINE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("100"), std::string::npos);
}

// --- §22.12: `line affects `__FILE__ ---

TEST(Preprocessor, Line_AffectsUnderscoreFileMacro) {
  PreprocFixture f;
  auto out = Preprocess("`line 1 \"overridden.sv\" 0\n`__FILE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("overridden.sv"), std::string::npos);
}

// --- §22.12: Line number increments after `line ---

TEST(Preprocessor, Line_IncrementAfterDirective) {
  PreprocFixture f;
  // `line 10 sets the *following* line to 10. Lines after increment.
  auto out =
      Preprocess("`line 10 \"f.sv\" 0\nfirst\n`__LINE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `__LINE__ is on source line 3. Override at source line 1.
  // Effective = 10 + (3 - 2) = 11.
  EXPECT_NE(out.find("11"), std::string::npos);
}

// --- §22.12: `line can appear anywhere ---

TEST(Preprocessor, Line_InsideModule_NoError) {
  PreprocFixture f;
  Preprocess("module m;\n`line 5 \"inner.sv\" 0\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.12: `line inside conditional compilation ---

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
  PreprocessWithPP(
      "`ifdef UNDEF_FLAG\n`line 99 \"cond.sv\" 0\n`endif\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.HasLineOverride());
}

// --- §22.12: Multiple `line directives, last wins ---

TEST(Preprocessor, Line_MultipleOverrides_LastWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 10 \"first.sv\" 0\n`line 20 \"second.sv\" 0\n", f,
                   pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineOffset(), 20u);
  EXPECT_EQ(pp.LineFile(), "second.sv");
}

// --- §22.12: Large line number ---

TEST(Preprocessor, Line_LargeLineNumber) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 999999 \"big.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.LineOffset(), 999999u);
}

// --- §22.12: Trailing whitespace after level is OK ---

TEST(Preprocessor, Line_TrailingWhitespaceAfterLevel_NoError) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0   \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}
