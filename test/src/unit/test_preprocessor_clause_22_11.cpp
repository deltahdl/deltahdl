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

}  // namespace
