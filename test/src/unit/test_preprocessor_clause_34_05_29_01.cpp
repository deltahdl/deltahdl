#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `runtime_license` protect pragma keyword
// (§34.5.29.1). The syntax block defines the keyword expression as a
// parenthesized subkeyword list: `runtime_license = ( library = <string> ,
// entry = <string> , feature = <string> [ , exit = <string> ]
// [ , match = <number> ] )`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including the entire parenthesized value.
struct ProtectRuntimeLicenseSyntaxTest : ::testing::Test {
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

// The fully populated keyword expression, carrying both optional subkeywords
// (`exit` and `match`) alongside the three required ones, is accepted and the
// directive line is stripped, including every subkeyword and value.
TEST_F(ProtectRuntimeLicenseSyntaxTest, PragmaProtectRuntimeLicenseConsumed) {
  auto result = Preprocess(
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" , match = 1 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("runtime_license"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
}

// Only the runtime_license directive line is removed; neighboring source text
// survives, confirming it is the runtime_license keyword expression line that
// the pragma path consumes.
TEST_F(ProtectRuntimeLicenseSyntaxTest,
       RuntimeLicenseDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" )\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two optional subkeywords are independent in the grammar
// (`[ , exit ] [ , match ]`): a form that omits `exit` but supplies `match` is
// a valid keyword expression and is consumed in full.
TEST_F(ProtectRuntimeLicenseSyntaxTest,
       RuntimeLicenseMatchWithoutExitConsumed) {
  auto result = Preprocess(
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , match = 0 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("match"), std::string::npos);
}

// The mirror image of the previous case: with the optionals independent, a form
// that supplies `exit` but omits `match` is also a valid keyword expression and
// is consumed in full. Together with the both/required-only/match-only forms
// this exhausts the four combinations of the two optional subkeywords.
TEST_F(ProtectRuntimeLicenseSyntaxTest,
       RuntimeLicenseExitWithoutMatchConsumed) {
  auto result = Preprocess(
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("release"), std::string::npos);
}

}  // namespace
