#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `key_public_key` protect pragma keyword
// (§34.5.26.1). The syntax block defines the keyword as the bare word
// `key_public_key` with no same-line argument (the encoded key value, if any,
// appears on a following line per the Description). Protect pragmas are
// processed at the preprocessor stage, where the generic `pragma` handler
// recognizes the keyword and consumes the directive line.
struct ProtectKeyPublicKeySyntaxTest : ::testing::Test {
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

// The bare `key_public_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectKeyPublicKeySyntaxTest, PragmaProtectKeyPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect key_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the key_public_key directive line is removed; neighboring source text
// survives, confirming it is the key_public_key keyword line that the pragma
// path consumes.
TEST_F(ProtectKeyPublicKeySyntaxTest,
       KeyPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect key_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as an encoded key
// value belongs to the Description, not the Syntax, of this keyword.)
TEST_F(ProtectKeyPublicKeySyntaxTest,
       KeyPublicKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result = Preprocess("`pragma protect key_public_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

}  // namespace
