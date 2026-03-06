#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

// --- §22.11: `pragma requires a pragma_name ---

TEST(Preprocessor, Pragma_MissingName_Error) {
  PreprocFixture f;
  Preprocess("`pragma\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_MissingName_OnlyWhitespace_Error) {
  PreprocFixture f;
  Preprocess("`pragma   \n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.11: `pragma with pragma_name (no expressions) ---

TEST(Preprocessor, Pragma_SimpleName_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Unrecognized pragma_names have no effect ---

TEST(Preprocessor, Pragma_UnrecognizedName_NoError) {
  PreprocFixture f;
  Preprocess("`pragma unknown_pragma_xyz\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: `pragma with pragma_expressions ---

TEST(Preprocessor, Pragma_NameWithKeyword_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma keyword1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_NameWithKeywordValue_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key1 = val1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_MultipleExpressions_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma expr1, expr2, expr3\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_NumberValue_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma 42\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_StringValue_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma \"hello world\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_ParenthesizedValue_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma (a, b, c)\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_ComplexExpression_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma key1 = (a, b), key2 = \"str\", 99\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Directive produces no output ---

TEST(Preprocessor, Pragma_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma some_pragma\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, Pragma_WithExpressions_NoOutput) {
  PreprocFixture f;
  auto out = Preprocess("`pragma my_pragma key = val, 42\n", f);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

// --- §22.11: Surrounding code is preserved ---

TEST(Preprocessor, Pragma_SurroundingCodePreserved) {
  PreprocFixture f;
  auto out = Preprocess("wire a;\n`pragma some_pragma\nwire b;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire a;"), std::string::npos);
  EXPECT_NE(out.find("wire b;"), std::string::npos);
}

// --- §22.11.1: `pragma reset resets named pragmas ---

TEST(Preprocessor, Pragma_Reset_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset my_pragma\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_Reset_MultipleNames_NoError) {
  PreprocFixture f;
  Preprocess("`pragma reset name1, name2, name3\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11.1: `pragma resetall resets all pragmas ---

TEST(Preprocessor, Pragma_Resetall_NoError) {
  PreprocFixture f;
  Preprocess("`pragma resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11.1: `pragma protect is recognized (Clause 34) ---

TEST(Preprocessor, Pragma_Protect_NoError) {
  PreprocFixture f;
  Preprocess("`pragma protect begin\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Pragma inside conditional compilation ---

TEST(Preprocessor, Pragma_InsideIfdef_Active) {
  PreprocFixture f;
  Preprocess("`define MY_FLAG\n`ifdef MY_FLAG\n`pragma some_pragma\n`endif\n",
             f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_InsideIfdef_Inactive) {
  PreprocFixture f;
  auto out = Preprocess("`ifdef UNDEF_FLAG\n`pragma some_pragma\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Pragma does not affect `resetall behavior ---
// `resetall does not reset pragma state per §22.3.

TEST(Preprocessor, Pragma_ResetallDoesNotAffectPragma) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`pragma some_pragma key=val\n", f, pp);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Pragma can appear inside design elements ---

TEST(Preprocessor, Pragma_InsideModule_NoError) {
  PreprocFixture f;
  Preprocess("module m;\n`pragma some_pragma\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Macro expansion within pragma ---

TEST(Preprocessor, Pragma_MacroExpansionInName) {
  PreprocFixture f;
  // Macro expansion in pragma arguments (§22.2: macro expansion occurs within
  // directives). The pragma_name itself is a simple_identifier from the
  // directive text, but expressions may contain macros.
  auto out = Preprocess("`define MY_VAL 42\n`pragma my_pragma `MY_VAL\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Edge case — pragma with only whitespace after name ---

TEST(Preprocessor, Pragma_NameTrailingWhitespace_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma   \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.11: Edge case — pragma at end of file without newline ---

TEST(Preprocessor, Pragma_NoTrailingNewline_NoError) {
  PreprocFixture f;
  Preprocess("`pragma my_pragma", f);
  EXPECT_FALSE(f.diag.HasErrors());
}
