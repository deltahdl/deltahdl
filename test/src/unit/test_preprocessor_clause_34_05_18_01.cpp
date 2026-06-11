#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `digest_keyname` protect pragma keyword
// (§34.5.18.1). The syntax block defines the keyword expression as
// `digest_keyname = <string>`. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// expression and consumes the directive line, including its string argument.
struct ProtectDigestKeynameSyntaxTest : ::testing::Test {
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

// The `digest_keyname = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestKeynameSyntaxTest, PragmaProtectDigestKeynameConsumed) {
  auto result = Preprocess("`pragma protect digest_keyname = \"key1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("key1"), std::string::npos);
}

// Only the digest_keyname directive line is removed; neighboring source text
// survives, confirming it is the digest_keyname keyword expression line that
// the pragma path consumes.
TEST_F(ProtectDigestKeynameSyntaxTest,
       DigestKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_keyname = \"key1\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case for the `<string>` operand: a multi-word, space-bearing value is
// consumed in full along with the directive, confirming the whole keyword
// expression (not just a leading token) is taken by the pragma path.
TEST_F(ProtectDigestKeynameSyntaxTest,
       DigestKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_keyname = \"project alpha key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("project alpha key"), std::string::npos);
}

}  // namespace
