#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Exercises the syntax of the `digest_public_key` protect pragma keyword
// (§34.5.19.1). The syntax block defines the keyword as the bare word
// `digest_public_key` with no same-line argument (the encoded key value, if
// any, appears on a following line per the Description). Protect pragmas are
// processed at the preprocessor stage, where the generic `pragma` handler
// recognizes the keyword and consumes the directive line.
struct ProtectDigestPublicKeySyntaxTest : ::testing::Test {
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

// The bare `digest_public_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDigestPublicKeySyntaxTest, PragmaProtectDigestPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect digest_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the digest_public_key directive line is removed; neighboring source text
// survives, confirming it is the digest_public_key keyword line that the pragma
// path consumes.
TEST_F(ProtectDigestPublicKeySyntaxTest,
       DigestPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as an encoded key
// value belongs to the Description, not the Syntax, of this keyword.)
TEST_F(ProtectDigestPublicKeySyntaxTest,
       DigestPublicKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result =
      Preprocess("`pragma protect digest_public_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

}  // namespace
