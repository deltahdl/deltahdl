#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(WhiteSpacePreprocessor, SpaceDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module t; logic a; endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, TabDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\tt;\tlogic\ta;\tendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, NewlineDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\nt\n;\nlogic\na\n;\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, FormfeedDelimiterPreserved) {
  PreprocFixture f;
  auto result = Preprocess("module\ft\f;\flogic\fa\f;\fendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(WhiteSpacePreprocessor, EmptyInputPreprocessesCleanly) {
  PreprocFixture f;
  auto result = Preprocess("", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
