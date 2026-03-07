// Non-LRM tests

#include <gtest/gtest.h>
#include "fixture_preprocessor.h"

using namespace delta;

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
