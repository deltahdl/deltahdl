#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `data_keyname` protect pragma keyword
// (§34.5.12.1). The syntax block defines the keyword expression as
// `data_keyname = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectDataKeynameSyntaxTest : ::testing::Test {
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

// The `data_keyname = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDataKeynameSyntaxTest, PragmaProtectDataKeynameConsumed) {
  auto result = Preprocess("`pragma protect data_keyname = \"primary-key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("primary-key"), std::string::npos);
}

// Only the data_keyname directive line is removed; neighboring source text
// survives, confirming it is the data_keyname keyword expression line that the
// pragma path consumes.
TEST_F(ProtectDataKeynameSyntaxTest,
       DataKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect data_keyname = \"primary-key\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case: the `<string>` value of the keyword expression may contain
// internal whitespace; the directive line is still consumed in full, with no
// portion of the quoted value leaking into the output.
TEST_F(ProtectDataKeynameSyntaxTest,
       DataKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect data_keyname = \"my key name\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("my key name"), std::string::npos);
}

}  // namespace
