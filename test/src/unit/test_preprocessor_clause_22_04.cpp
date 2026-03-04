#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, Include_AbsolutePath) {
  PreprocFixture f;
  auto result = Preprocess("`include \"/dev/null\"\nmodule m; endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

TEST(Preprocessor, IncludeFilenameStripsComment) {
  PreprocFixture f;

  Preprocess("`include \"nonexistent.sv\" // this is a comment\n", f);

  EXPECT_TRUE(f.diag.HasErrors());
}
