#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `comment` protect pragma keyword (§34.5.30.1).
// The syntax block defines the keyword expression as `comment = <string>`.
// Protect pragmas are processed at the preprocessor stage, where the generic
// `pragma` handler recognizes the keyword expression and consumes the directive
// line, including its string argument.
struct ProtectCommentSyntaxTest : ::testing::Test {
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

// The `comment = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectCommentSyntaxTest, PragmaProtectCommentConsumed) {
  auto result = Preprocess("`pragma protect comment = \"acme notice\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme notice"), std::string::npos);
}

// Only the comment directive line is removed; neighboring source text survives,
// confirming it is the comment keyword expression line that the pragma path
// consumes.
TEST_F(ProtectCommentSyntaxTest, CommentDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect comment = \"acme notice\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The <string> argument of the keyword expression may carry embedded
// whitespace; the entire quoted value is consumed along with the directive
// line, exercising the <string> portion of `comment = <string>`.
TEST_F(ProtectCommentSyntaxTest, CommentStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect comment = \"copyright 2026 acme inc\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("copyright 2026 acme inc"), std::string::npos);
}

}  // namespace
