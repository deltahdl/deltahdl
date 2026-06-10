#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `begin` protect pragma keyword (§34.5.1.1). The
// syntax block defines the keyword as the bare word `begin` with no arguments.
// Protect pragmas are processed at the preprocessor stage, where the generic
// `pragma` handler recognizes the keyword and consumes the directive line.
struct ProtectBeginSyntaxTest : ::testing::Test {
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

// The bare `begin` keyword is accepted and the directive line is stripped.
TEST_F(ProtectBeginSyntaxTest, PragmaProtectBeginConsumed) {
  auto result = Preprocess("`pragma protect begin\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the begin directive line is removed; neighboring source text survives,
// confirming it is the begin keyword line that the pragma path consumes.
TEST_F(ProtectBeginSyntaxTest, BeginDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect begin\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

}  // namespace
