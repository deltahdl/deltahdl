#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `key_keyname` protect pragma keyword
// (§34.5.25.1). The syntax block defines the keyword expression as
// `key_keyname = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectKeyKeynameSyntaxTest : ::testing::Test {
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

// The `key_keyname = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectKeyKeynameSyntaxTest, PragmaProtectKeyKeynameConsumed) {
  auto result = Preprocess("`pragma protect key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme-key"), std::string::npos);
}

// Only the key_keyname directive line is removed; neighboring source text
// survives, confirming it is the key_keyname keyword expression line that the
// pragma path consumes.
TEST_F(ProtectKeyKeynameSyntaxTest,
       KeyKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_keyname = \"acme-key\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The <string> argument of the keyword expression may carry embedded
// whitespace; the entire quoted value is consumed along with the directive
// line, exercising the <string> portion of `key_keyname = <string>`.
TEST_F(ProtectKeyKeynameSyntaxTest,
       KeyKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect key_keyname = \"acme rsa key 1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme rsa key 1"), std::string::npos);
}

}  // namespace
