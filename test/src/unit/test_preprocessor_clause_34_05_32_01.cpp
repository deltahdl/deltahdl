#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `viewport` protect pragma keyword (§34.5.32.1).
// The syntax block defines the keyword expression as a parenthesized subkeyword
// list with two required string subkeywords:
// `viewport = ( object = <string> , access = <string> )`. Protect pragmas are
// processed at the preprocessor stage, where the generic `pragma` handler
// recognizes the keyword expression and consumes the directive line, including
// the entire parenthesized value.
struct ProtectViewportSyntaxTest : ::testing::Test {
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

// The fully populated `viewport = ( object = <string> , access = <string> )`
// keyword expression is accepted and the directive line is stripped, including
// both subkeywords and their string values.
TEST_F(ProtectViewportSyntaxTest, PragmaProtectViewportConsumed) {
  auto result = Preprocess(
      "`pragma protect viewport = ( object = \"top.dut\" , access = \"r\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("viewport"), std::string::npos);
  EXPECT_EQ(result.find("top.dut"), std::string::npos);
}

// Only the viewport directive line is removed; neighboring source text survives,
// confirming it is the viewport keyword expression line that the pragma path
// consumes.
TEST_F(ProtectViewportSyntaxTest, ViewportDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect viewport = ( object = \"top.dut\" , access = \"rw\" )\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("top.dut"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The grammar requires two <string> subkeyword values (`object` and `access`).
// Either value may carry embedded whitespace; the entire parenthesized list,
// including both quoted strings, is consumed along with the directive line,
// exercising the <string> portions of the keyword expression.
TEST_F(ProtectViewportSyntaxTest,
       ViewportObjectAndAccessStringArgumentsConsumed) {
  auto result = Preprocess(
      "`pragma protect viewport = ( object = \"top.dut.mem array\" , "
      "access = \"read only\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("object"), std::string::npos);
  EXPECT_EQ(result.find("access"), std::string::npos);
  EXPECT_EQ(result.find("top.dut.mem array"), std::string::npos);
  EXPECT_EQ(result.find("read only"), std::string::npos);
}

}  // namespace
