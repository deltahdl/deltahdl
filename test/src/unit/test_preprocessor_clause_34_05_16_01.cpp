#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `digest_keyowner` protect pragma keyword
// (§34.5.16.1). The syntax block defines the keyword expression as
// `digest_keyowner = <string>`. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// expression and consumes the directive line, including its string argument.
struct ProtectDigestKeyownerSyntaxTest : ::testing::Test {
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

// The `digest_keyowner = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestKeyownerSyntaxTest, PragmaProtectDigestKeyownerConsumed) {
  auto result = Preprocess("`pragma protect digest_keyowner = \"Acme Corp\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Acme Corp"), std::string::npos);
}

// Only the digest_keyowner directive line is removed; neighboring source text
// survives, confirming it is the digest_keyowner keyword expression line that
// the pragma path consumes.
TEST_F(ProtectDigestKeyownerSyntaxTest,
       DigestKeyownerDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_keyowner = \"Acme "
      "Corp\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

}  // namespace
