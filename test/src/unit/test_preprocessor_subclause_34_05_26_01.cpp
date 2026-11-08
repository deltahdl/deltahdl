#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

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

TEST_F(ProtectKeyPublicKeySyntaxTest, PragmaProtectKeyPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect key_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectKeyPublicKeySyntaxTest,
       KeyPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect key_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectKeyPublicKeySyntaxTest,
       KeyPublicKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result = Preprocess("`pragma protect key_public_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

constexpr std::string_view kDesignatedKey = "acme-public-key-of-2027";
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyItReaches = "meridian-trust-wrapping-key";

std::string Encoded(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

std::string NamesTheEntity() {
  std::string text = "`pragma protect key_keyowner=\"";
  text.append(kEntity).append("\"\n");
  return text;
}

std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

std::string AnnouncesTheKey() {
  std::string text = "`pragma protect key_public_key\n";
  text.append(Encoded(kDesignatedKey)).append("\n");
  return text;
}

TEST(ProtectKeyPublicKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  EXPECT_EQ(ReadKeywordScope(EnvelopeCarrying(AnnouncesTheKey()))
                .ValueOf(kKeyPublicKeyKeyword)
                .value,
            kDesignatedKey);
}

TEST(ProtectKeyPublicKeySyntax, TheLineTheKeywordSpokeForIsNotDesignText) {
  ReadKeywordScope run(EnvelopeCarrying(AnnouncesTheKey()));
  EXPECT_FALSE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

TEST(ProtectKeyPublicKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string described = "`pragma protect key_public_key=\"stated-here\"\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  ReadKeywordScope run(EnvelopeCarrying(described));
  EXPECT_EQ(run.ValueOf(kKeyPublicKeyKeyword).value, "stated-here");
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

TEST(ProtectKeyPublicKeySyntax, AListAgainstTheKeywordSpeaksForNoLine) {
  std::string described =
      "`pragma protect key_public_key=(held_by=\"meridian-trust\")\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  ReadKeywordScope run(EnvelopeCarrying(described));
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

TEST(ProtectKeyPublicKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  std::string described = "`pragma protect key_public_key_of_theirs\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  ReadKeywordScope run(EnvelopeCarrying(described));
  EXPECT_TRUE(run.ValueOf(kKeyPublicKeyKeyword).defaulted);
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

TEST(ProtectKeyPublicKeySyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  std::string described =
      "`pragma protect key_keyowner=\"meridian-trust\", key_public_key\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  EXPECT_EQ(ReadKeywordScope(EnvelopeCarrying(described))
                .ValueOf(kKeyPublicKeyKeyword)
                .value,
            kDesignatedKey);
}

TEST(ProtectKeyPublicKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_public_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectKeyPublicKeySyntax, TheAnnouncementIsReadOnlyInsideAnEnvelope) {
  ReadKeywordScope run(AnnouncesTheKey());
  EXPECT_TRUE(run.ValueOf(kKeyPublicKeyKeyword).value.empty());
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

TEST(ProtectKeyPublicKeySyntax, TheDesignationReachesTheKeyItNames) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kDesignatedKey, kKeyItReaches));
  EXPECT_EQ(
      ReadKeywordScope(EnvelopeCarrying(NamesTheEntity() + AnnouncesTheKey()))
          .KeyBlockKeyReached(keys),
      kKeyItReaches);
}

}  // namespace
