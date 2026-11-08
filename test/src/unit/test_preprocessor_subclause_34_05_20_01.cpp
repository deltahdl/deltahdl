#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"

using namespace delta;

struct ProtectDigestDecryptKeySyntaxTest : ::testing::Test {
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

TEST_F(ProtectDigestDecryptKeySyntaxTest,
       PragmaProtectDigestDecryptKeyConsumed) {
  auto result = Preprocess("`pragma protect digest_decrypt_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectDigestDecryptKeySyntaxTest,
       DigestDecryptKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_decrypt_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDigestDecryptKeySyntaxTest,
       DigestDecryptKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result =
      Preprocess("`pragma protect digest_decrypt_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

constexpr std::string_view kSharedValue = "one-value-in-two-places";

constexpr std::string_view kRepetition =
    "writes one value against two of the names that designate a key of the "
    "digest_keyowner in effect";

std::string EncodedValue(std::string_view value) {
  return EncodeProtectBlock(value, DefaultProtectEncoding());
}

std::string NamesTheDigestKey(std::string_view value) {
  std::string text = "`pragma protect digest_keyname=\"";
  text.append(value).append("\"\n");
  return text;
}

std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};

  explicit ReadEnvelope(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

TEST(ProtectDigestDecryptKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  std::string src = EnvelopeCarrying(NamesTheDigestKey(kSharedValue) +
                                     "`pragma protect digest_decrypt_key\n" +
                                     EncodedValue(kSharedValue) + "\n");
  ReadEnvelope run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), kRepetition,
                            LineHolding(src, EncodedValue(kSharedValue)),
                            "34.5.16"));
}

TEST(ProtectDigestDecryptKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  ReadEnvelope run(EnvelopeCarrying(
      NamesTheDigestKey(kSharedValue) +
      "`pragma protect digest_decrypt_key=\"a-value-of-its-own\"\n" +
      EncodedValue(kSharedValue) + "\n"));
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectDigestDecryptKeySyntax,
     TheKeywordStandsAloneAmongOtherExpressions) {
  std::string src = EnvelopeCarrying(
      "`pragma protect digest_keyname=\"one-value-in-two-places\", "
      "digest_decrypt_key\n" +
      EncodedValue(kSharedValue) + "\n");
  ReadEnvelope run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), kRepetition,
                            LineHolding(src, EncodedValue(kSharedValue)),
                            "34.5.16"));
}

TEST(ProtectDigestDecryptKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_decrypt_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDigestDecryptKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadEnvelope run(
      EnvelopeCarrying(NamesTheDigestKey(kSharedValue) +
                       "`pragma protect digest_decrypt_key_of_theirs\n" +
                       EncodedValue(kSharedValue) + "\n"));
  EXPECT_FALSE(run.diag.HasErrors());
}

}  // namespace
