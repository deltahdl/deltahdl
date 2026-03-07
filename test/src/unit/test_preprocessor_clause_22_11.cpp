// §22.11

#include <gtest/gtest.h>
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

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

}  // namespace
