#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `begin_protected` protect pragma keyword
// (§34.5.3.1). The syntax block defines the keyword as the bare word
// `begin_protected` with no arguments. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the
// keyword and consumes the directive line.
struct ProtectBeginProtectedSyntaxTest : ::testing::Test {
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

// The bare `begin_protected` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectBeginProtectedSyntaxTest, PragmaProtectBeginProtectedConsumed) {
  auto result = Preprocess("`pragma protect begin_protected\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the begin_protected directive line is removed; neighboring source text
// survives, confirming it is the begin_protected keyword line that the pragma
// path consumes.
TEST_F(ProtectBeginProtectedSyntaxTest,
       BeginProtectedDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect begin_protected\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

}  // namespace
