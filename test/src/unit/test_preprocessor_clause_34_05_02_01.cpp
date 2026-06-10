#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `end` protect pragma keyword (§34.5.2.1). The
// syntax block defines the keyword as the bare word `end` with no arguments.
// Protect pragmas are processed at the preprocessor stage, where the generic
// `pragma` handler recognizes the keyword and consumes the directive line.
struct ProtectEndSyntaxTest : ::testing::Test {
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

// The bare `end` keyword is accepted and the directive line is stripped.
TEST_F(ProtectEndSyntaxTest, PragmaProtectEndConsumed) {
  auto result = Preprocess("`pragma protect end\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the end directive line is removed; neighboring source text survives,
// confirming it is the end keyword line that the pragma path consumes.
TEST_F(ProtectEndSyntaxTest, EndDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect end\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

}  // namespace
