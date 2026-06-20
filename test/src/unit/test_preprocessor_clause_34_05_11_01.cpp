#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `data_method` protect pragma keyword
// (§34.5.11.1). The syntax block defines the keyword expression as
// `data_method = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectDataMethodSyntaxTest : ::testing::Test {
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

// The `data_method = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDataMethodSyntaxTest, PragmaProtectDataMethodConsumed) {
  auto result = Preprocess("`pragma protect data_method = \"aes128-cbc\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("aes128-cbc"), std::string::npos);
}

// Only the data_method directive line is removed; neighboring source text
// survives, confirming it is the data_method keyword expression line that the
// pragma path consumes.
TEST_F(ProtectDataMethodSyntaxTest,
       DataMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect data_method = \"aes128-cbc\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case: the `<string>` value of the keyword expression may contain
// internal whitespace; the directive line is still consumed in full, with no
// portion of the quoted value leaking into the output.
TEST_F(ProtectDataMethodSyntaxTest,
       DataMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect data_method = \"my custom cipher\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("my custom cipher"), std::string::npos);
}

}  // namespace
