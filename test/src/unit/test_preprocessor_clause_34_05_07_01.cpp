#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `encrypt_agent` protect pragma keyword
// (§34.5.7.1). The syntax block defines the keyword expression as
// `encrypt_agent = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectEncryptAgentSyntaxTest : ::testing::Test {
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

// The `encrypt_agent = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectEncryptAgentSyntaxTest, PragmaProtectEncryptAgentConsumed) {
  auto result = Preprocess("`pragma protect encrypt_agent = \"AcmeCrypt\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("AcmeCrypt"), std::string::npos);
}

// Only the encrypt_agent directive line is removed; neighboring source text
// survives, confirming it is the encrypt_agent keyword expression line that the
// pragma path consumes.
TEST_F(ProtectEncryptAgentSyntaxTest,
       EncryptAgentDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect encrypt_agent = \"AcmeCrypt\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The `<string>` argument of the keyword expression is consumed in full
// regardless of its contents: a quoted value with embedded spaces and
// punctuation is still stripped along with the directive line.
TEST_F(ProtectEncryptAgentSyntaxTest, EncryptAgentStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect encrypt_agent = \"Acme Crypt v2.0\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Acme Crypt"), std::string::npos);
}

}  // namespace
