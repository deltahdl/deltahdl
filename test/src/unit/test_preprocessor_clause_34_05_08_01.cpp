#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `encrypt_agent_info` protect pragma keyword
// (§34.5.8.1). The syntax block defines the keyword expression as
// `encrypt_agent_info = <string>`. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// expression and consumes the directive line, including its string argument.
struct ProtectEncryptAgentInfoSyntaxTest : ::testing::Test {
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

// The `encrypt_agent_info = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectEncryptAgentInfoSyntaxTest, PragmaProtectEncryptAgentInfoConsumed) {
  auto result =
      Preprocess("`pragma protect encrypt_agent_info = \"AcmeCrypt 3.1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("AcmeCrypt"), std::string::npos);
}

// Only the encrypt_agent_info directive line is removed; neighboring source text
// survives, confirming it is the encrypt_agent_info keyword expression line that
// the pragma path consumes.
TEST_F(ProtectEncryptAgentInfoSyntaxTest,
       EncryptAgentInfoDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect encrypt_agent_info = \"AcmeCrypt 3.1\"\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The `<string>` argument of the keyword expression is consumed in full
// regardless of its contents: a quoted value with embedded spaces and
// punctuation is still stripped along with the directive line.
TEST_F(ProtectEncryptAgentInfoSyntaxTest,
       EncryptAgentInfoStringArgumentWithSpacesConsumed) {
  auto result = Preprocess(
      "`pragma protect encrypt_agent_info = \"Built by Acme, rev 2.0\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Built by Acme"), std::string::npos);
}

}  // namespace
