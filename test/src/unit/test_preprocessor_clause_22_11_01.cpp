

#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

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

}  // namespace
