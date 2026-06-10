#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `author` protect pragma keyword (§34.5.5.1). The
// syntax block defines the keyword expression as `author = <string>`. Protect
// pragmas are processed at the preprocessor stage, where the generic `pragma`
// handler recognizes the keyword expression and consumes the directive line,
// including its string argument.
struct ProtectAuthorSyntaxTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

// The `author = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectAuthorSyntaxTest, PragmaProtectAuthorConsumed) {
  auto result = Preprocess("`pragma protect author = \"Jane Doe\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Jane Doe"), std::string::npos);
}

// Only the author directive line is removed; neighboring source text survives,
// confirming it is the author keyword expression line that the pragma path
// consumes.
TEST_F(ProtectAuthorSyntaxTest, AuthorDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect author = \"Jane Doe\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

}  // namespace
