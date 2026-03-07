// Non-LRM tests

#include <gtest/gtest.h>
#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

namespace {

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

// --- §22.11.1: `pragma protect is recognized (Clause 34) ---
TEST(Preprocessor, Pragma_Protect_NoError) {
  PreprocFixture f;
  Preprocess("`pragma protect begin\n", f);
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

}  // namespace
