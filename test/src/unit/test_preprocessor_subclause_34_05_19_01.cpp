#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

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

TEST_F(ProtectDigestPublicKeySyntaxTest, PragmaProtectDigestPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect digest_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectDigestPublicKeySyntaxTest,
       DigestPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDigestPublicKeySyntaxTest,
       DigestPublicKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result =
      Preprocess("`pragma protect digest_public_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

constexpr std::string_view kDesignatedKey = "veritas-rsa-public-key";

struct ReadDigestPublicKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadDigestPublicKey(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue Designated() const {
    return pp.ProtectKeywords().ValueOf(kDigestPublicKeyKeyword);
  }
};

std::string Encoded(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

TEST(ProtectDigestPublicKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  std::string described = "`pragma protect digest_public_key\n";
  described += Encoded(kDesignatedKey) + "\n";
  ReadDigestPublicKey run(EnvelopeCarrying(described));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Designated().value, kDesignatedKey);
}

TEST(ProtectDigestPublicKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string described = "`pragma protect digest_public_key=\"stated-here\"\n";
  described += Encoded(kDesignatedKey) + "\n";
  ReadDigestPublicKey run(EnvelopeCarrying(described));
  EXPECT_EQ(run.Designated().value, "stated-here");
}

TEST(ProtectDigestPublicKeySyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  std::string described =
      "`pragma protect digest_keyowner=\"veritas\", digest_public_key\n";
  described += Encoded(kDesignatedKey) + "\n";
  ReadDigestPublicKey run(EnvelopeCarrying(described));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Designated().value, kDesignatedKey);
}

TEST(ProtectDigestPublicKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_public_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDigestPublicKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadDigestPublicKey run(
      "`pragma protect digest_public_key_of_theirs=\"k\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Designated().defaulted);
}

}  // namespace
