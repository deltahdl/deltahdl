#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kVouchedDesign = "module vouched_m; endmodule\n";

constexpr std::string_view kSignatureProvider = "harbor-mark-custody";
constexpr std::string_view kSignatureName = "wrapping-2041";
constexpr std::string_view kSignatureKey = "harbor-mark-wrapping-key";

constexpr std::string_view kDesignProvider = "orrery-labs";
constexpr std::string_view kDesignName = "design-2041";
constexpr std::string_view kDesignKey = "orrery-labs-region-key";

constexpr std::string_view kDigestProvider = "solace-notary";
constexpr std::string_view kDigestName = "notary-2041";
constexpr std::string_view kDigestKey = "solace-notary-signing-key";

constexpr std::string_view kKeyBlockExpression = "`pragma protect key_block\n";

constexpr std::string_view kDigestBlockExpression =
    "`pragma protect digest_block\n";

constexpr std::string_view kDigestKeyBlockExpression =
    "`pragma protect digest_key_block";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string NamesTheDigestProvider() {
  return Writes("digest_keyowner", kDigestProvider);
}

std::string RegionAskingForADigestWith(const std::string& key_provider) {
  std::string text = "`pragma protect begin\n";
  text.append(kDigestBlockExpression);
  text.append(Writes("data_keyowner", kDesignProvider));
  text.append(Writes("data_keyname", kDesignName));
  text.append(NamesTheDigestProvider());
  text.append(Writes("digest_keyname", kDigestName));
  text.append(key_provider);
  text.append(kVouchedDesign);
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAskingForADigest() {
  return RegionAskingForADigestWith(Writes("key_keyowner", kSignatureProvider) +
                                    Writes("key_keyname", kSignatureName));
}

ProtectKeyList KeysWithoutTheDesignsOwnKey() {
  ProtectKeyList held;
  held.Add(KeyOf(kSignatureProvider, kSignatureName, kSignatureKey));
  held.Add(KeyOf(kDigestProvider, kDigestName, kDigestKey));
  return held;
}

ProtectKeyList KeysReachingTheDesignsOwnKey() {
  ProtectKeyList held;
  held.Add(KeyOf(kSignatureProvider, kSignatureName, kSignatureKey));
  held.Add(KeyOf(kDigestProvider, kDigestName, kDigestKey));
  held.Add(KeyOf(kDesignProvider, kDesignName, kDesignKey));
  return held;
}

std::string EnvelopeUnder(const std::string& region,
                          const ProtectKeyList& held) {
  std::string envelope = EncryptEnvelopes(region, {}, held);
  EXPECT_FALSE(Holds(envelope, kVouchedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, kDigestBlockExpression)) << envelope;
  return envelope;
}

std::string SignedEnvelope() {
  return EnvelopeUnder(RegionAskingForADigest(), KeysWithoutTheDesignsOwnKey());
}

std::string PlainEnvelope() {
  return EnvelopeUnder(RegionAskingForADigestWith(""),
                       KeysReachingTheDesignsOwnKey());
}

TEST(ProtectDigestKeyownerSignedEnvelope,
     TheEntityStandsInTheClearInASignedEnvelope) {
  std::string envelope = SignedEnvelope();
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 1U) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDigestProvider())) << envelope;
}

TEST(ProtectDigestKeyownerSignedEnvelope,
     TheEntityStandsInTheClearWithoutASignature) {
  std::string envelope = PlainEnvelope();
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 0U) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDigestProvider())) << envelope;
}

TEST(ProtectDigestKeyownerSignedEnvelope,
     NoDigestKeyBlockIsWrittenForTheEntityToTravelIn) {
  std::string signed_envelope = SignedEnvelope();
  EXPECT_FALSE(Holds(signed_envelope, kDigestKeyBlockExpression))
      << signed_envelope;
  std::string plain_envelope = PlainEnvelope();
  EXPECT_FALSE(Holds(plain_envelope, kDigestKeyBlockExpression))
      << plain_envelope;
}

TEST(ProtectDigestKeyownerSignedEnvelope,
     TheSignedEnvelopeOpensWithTheEntityInTheClear) {
  PreprocFixture fixture;
  PreprocConfig config;
  config.protect_keys = KeysWithoutTheDesignsOwnKey();
  std::string recovered = Preprocess(SignedEnvelope(), fixture, config);
  EXPECT_FALSE(fixture.diag.HasErrors()) << recovered;
  EXPECT_TRUE(Holds(recovered, kVouchedDesign)) << recovered;
}

}  // namespace
