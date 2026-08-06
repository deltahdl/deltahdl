#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `digest_method` protect pragma keyword
// (§34.5.21.1). The syntax block defines the keyword expression as
// `digest_method = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectDigestMethodSyntaxTest : ::testing::Test {
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

// The `digest_method = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestMethodSyntaxTest, PragmaProtectDigestMethodConsumed) {
  auto result = Preprocess("`pragma protect digest_method = \"sha256\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha256"), std::string::npos);
}

// Only the digest_method directive line is removed; neighboring source text
// survives, confirming it is the digest_method keyword expression line that the
// pragma path consumes.
TEST_F(ProtectDigestMethodSyntaxTest,
       DigestMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_method = \"sha256\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case for the `<string>` operand: a multi-word, space-bearing value is
// consumed in full along with the directive, confirming the whole keyword
// expression (not just a leading token) is taken by the pragma path.
TEST_F(ProtectDigestMethodSyntaxTest,
       DigestMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_method = \"sha 512 variant\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha 512 variant"), std::string::npos);
}

}  // namespace
