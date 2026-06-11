#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `key_method` protect pragma keyword
// (§34.5.24.1). The syntax block defines the keyword expression as
// `key_method = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectKeyMethodSyntaxTest : ::testing::Test {
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

// The `key_method = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectKeyMethodSyntaxTest, PragmaProtectKeyMethodConsumed) {
  auto result = Preprocess("`pragma protect key_method = \"rsa\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("rsa"), std::string::npos);
}

// Only the key_method directive line is removed; neighboring source text
// survives, confirming it is the key_method keyword expression line that the
// pragma path consumes.
TEST_F(ProtectKeyMethodSyntaxTest,
       KeyMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_method = \"rsa\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The <string> argument of the keyword expression may carry embedded
// whitespace; the entire quoted value is consumed along with the directive
// line, exercising the <string> portion of `key_method = <string>`.
TEST_F(ProtectKeyMethodSyntaxTest, KeyMethodStringArgumentWithSpacesConsumed) {
  auto result = Preprocess("`pragma protect key_method = \"aes 128 cbc\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("aes 128 cbc"), std::string::npos);
}

}  // namespace
