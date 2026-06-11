#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `key_block` protect pragma keyword (§34.5.27.1).
// The syntax block defines the keyword as the bare word `key_block` with no
// same-line argument (the encoded key block content, if any, appears on a
// following line per the Description). Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// and consumes the directive line.
struct ProtectKeyBlockSyntaxTest : ::testing::Test {
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

// The bare `key_block` keyword is accepted and the directive line is stripped.
TEST_F(ProtectKeyBlockSyntaxTest, PragmaProtectKeyBlockConsumed) {
  auto result = Preprocess("`pragma protect key_block\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the key_block directive line is removed; neighboring source text
// survives, confirming it is the key_block keyword line that the pragma path
// consumes.
TEST_F(ProtectKeyBlockSyntaxTest,
       KeyBlockDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect key_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as encoded key block
// content belongs to the Description, not the Syntax, of this keyword.)
TEST_F(ProtectKeyBlockSyntaxTest,
       KeyBlockConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result = Preprocess("`pragma protect key_block\nENCODEDKEYBLOCKDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("ENCODEDKEYBLOCKDATA"), std::string::npos);
}

}  // namespace
