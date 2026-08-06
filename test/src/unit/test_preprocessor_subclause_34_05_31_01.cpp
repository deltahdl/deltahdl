#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `reset` protect pragma keyword (§34.5.31.1).
// The syntax block defines the keyword as the bare word `reset` with no
// arguments. Protect pragmas are processed at the preprocessor stage, where the
// generic `pragma` handler recognizes the keyword and consumes the directive
// line.
struct ProtectResetSyntaxTest : ::testing::Test {
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

// The bare `reset` keyword is accepted and the directive line is stripped.
TEST_F(ProtectResetSyntaxTest, PragmaProtectResetConsumed) {
  auto result = Preprocess("`pragma protect reset\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("reset"), std::string::npos);
}

// Only the reset directive line is removed; neighboring source text survives,
// confirming it is the reset keyword line that the pragma path consumes.
TEST_F(ProtectResetSyntaxTest, ResetDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect reset\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

}  // namespace
