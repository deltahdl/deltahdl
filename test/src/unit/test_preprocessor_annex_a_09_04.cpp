#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// §A.9.4: white_space ::= space | tab | newline | formfeed | eof — observed at
// the preprocessor stage: each non-EOF alternative must traverse preprocessing
// without producing errors.

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

// §A.9.4 eof alternative (degenerate form): empty source must preprocess
// without errors — EOF is the only white_space and there are no tokens.
TEST(WhiteSpacePreprocessor, EmptyInputPreprocessesCleanly) {
  PreprocFixture f;
  auto result = Preprocess("", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
