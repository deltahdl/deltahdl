#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kProvider = "veritas-signing";
constexpr std::string_view kOtherProvider = "globex-ip";

constexpr std::string_view kPublicKey = "veritas-rsa-public-key";
constexpr std::string_view kKeyName = "veritas-digest-2027";

constexpr std::string_view kDigestKey = "veritas-digest-signing-key";
constexpr std::string_view kOtherDigestKey = "veritas-some-other-key-entirely";

constexpr std::string_view kDataPublicKey = "veritas-rsa-data-public-key";

constexpr std::string_view kExchangeKey = "veritas-region-exchange-key";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kDisagreement =
    "digest_public_key and digest_keyname designate different keys of the "
    "digest_keyowner in effect";

ProtectEncoding PlainEncoding() { return DefaultProtectEncoding(); }

ProtectEncoding Base64Encoding() {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBase64Enctype);
  return encoding;
}

std::string StatesEncoding(std::string_view enctype) {
  std::string text = "`pragma protect encoding=(enctype=\"";
  text.append(enctype).append("\")\n");
  return text;
}

std::string NamesProvider(std::string_view provider) {
  std::string text = "`pragma protect digest_keyowner=\"";
  text.append(provider).append("\"\n");
  return text;
}

std::string NamesDigestKey(std::string_view keyname) {
  std::string text = "`pragma protect digest_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

std::string DigestPublicKeyDesignation(std::string_view key,
                                       const ProtectEncoding& encoding) {
  std::string text = "`pragma protect digest_public_key\n";
  text.append(EncodeProtectBlock(key, encoding)).append("\n");
  return text;
}

std::string DataPublicKeyDesignation(std::string_view key) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(key, PlainEncoding())).append("\n");
  return text;
}

std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

ProtectKeyList OneKeyUnder(std::string_view owner, std::string_view designation,
                           std::string_view key) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(designation), std::string(key)});
  return keys;
}

ProtectKeyList KeysUnderBothDesignations(std::string_view under_public,
                                         std::string_view under_name) {
  ProtectKeyList keys;
  keys.Add({std::string(kProvider), std::string(kPublicKey),
            std::string(under_public)});
  keys.Add(
      {std::string(kProvider), std::string(kKeyName), std::string(under_name)});
  return keys;
}

struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys)
      : pp(mgr, diag, Configured(keys)) {
    pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig Configured(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }

  ProtectKeywordValue Designated() const {
    return pp.ProtectKeywords().DigestPublicKeyInEffect();
  }

  std::string_view DigestBlockKey() const {
    return pp.DigestBlockKeyInEffect();
  }
};

std::string WrittenOutOf(const std::string& src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

TEST(ProtectDigestPublicKeyDescription, TheLineBeneathTheKeywordIsTheValue) {
  ReadUnderKeys run(
      ForeignEnvelope(DigestPublicKeyDesignation(kPublicKey, PlainEncoding())),
      ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kPublicKey);
}

TEST(ProtectDigestPublicKeyDescription, TheEncodingInEffectReadsTheLine) {
  std::string described = StatesEncoding(kBase64Enctype);
  described += DigestPublicKeyDesignation(kPublicKey, Base64Encoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kPublicKey);
}

TEST(ProtectDigestPublicKeyDescription, ALineReadUnderAnotherSchemeIsNotIt) {
  ReadUnderKeys run(
      ForeignEnvelope(DigestPublicKeyDesignation(kPublicKey, Base64Encoding())),
      ProtectKeyList());
  EXPECT_NE(run.Designated().value, kPublicKey);
}

TEST(ProtectDigestPublicKeyDescription, TheDesignationAndTheEntityReachOneKey) {
  std::string described = NamesProvider(kProvider);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    OneKeyUnder(kProvider, kPublicKey, kDigestKey));
  EXPECT_EQ(run.DigestBlockKey(), kDigestKey);
}

TEST(ProtectDigestPublicKeyDescription,
     ThatDesignationUnderAnotherPartyReachesNone) {
  std::string described = NamesProvider(kOtherProvider);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    OneKeyUnder(kProvider, kPublicKey, kDigestKey));
  EXPECT_TRUE(run.DigestBlockKey().empty());
}

TEST(ProtectDigestPublicKeyAgreement, TwoDesignationsReachingTwoKeysReported) {
  std::string described = NamesProvider(kProvider);
  described += NamesDigestKey(kKeyName);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  std::string envelope = ForeignEnvelope(described);
  ReadUnderKeys run(envelope,
                    KeysUnderBothDesignations(kDigestKey, kOtherDigestKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), kDisagreement,
      LineHolding(envelope, EncodeProtectBlock(kPublicKey, PlainEncoding())),
      "34.5.19"));
}

TEST(ProtectDigestPublicKeyAgreement, TwoDesignationsReachingOneKeyAccepted) {
  std::string described = NamesProvider(kProvider);
  described += NamesDigestKey(kKeyName);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeysUnderBothDesignations(kDigestKey, kDigestKey));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectDigestPublicKeyAgreement, TheNameWrittenLastCompletesThePair) {
  std::string described = NamesProvider(kProvider);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  described += NamesDigestKey(kKeyName);
  std::string envelope = ForeignEnvelope(described);
  ReadUnderKeys run(envelope,
                    KeysUnderBothDesignations(kDigestKey, kOtherDigestKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), kDisagreement,
      LineHolding(envelope, "`pragma protect digest_keyname"), "34.5.19"));
}

TEST(ProtectDigestPublicKeyAgreement,
     OneDesignationReachingNothingDecidesNone) {
  std::string described = NamesProvider(kProvider);
  described += NamesDigestKey(kKeyName);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    OneKeyUnder(kProvider, kKeyName, kOtherDigestKey));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectDigestPublicKeyDefault, TheDataDesignationFillsThePlaceLeftEmpty) {
  ReadUnderKeys run(ForeignEnvelope(DataPublicKeyDesignation(kDataPublicKey)),
                    ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kDataPublicKey);
}

TEST(ProtectDigestPublicKeyDefault, ThePlaceFilledFromTheDataIsADefault) {
  ReadUnderKeys run(ForeignEnvelope(DataPublicKeyDesignation(kDataPublicKey)),
                    ProtectKeyList());
  EXPECT_TRUE(run.Designated().defaulted);
}

TEST(ProtectDigestPublicKeyDefault, ADesignationForTheDigestIsNoDefault) {
  std::string described = DataPublicKeyDesignation(kDataPublicKey);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_FALSE(run.Designated().defaulted);
}

TEST(ProtectDigestPublicKeyDefault, ADesignationForTheDigestIsWhatStands) {
  std::string described = DataPublicKeyDesignation(kDataPublicKey);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kPublicKey);
}

TEST(ProtectDigestPublicKeyDefault, AnEmptyLineDesignatesNone) {
  std::string described = DataPublicKeyDesignation(kDataPublicKey);
  described += DigestPublicKeyDesignation("", PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kDataPublicKey);
  EXPECT_TRUE(run.Designated().defaulted);
}

TEST(ProtectDigestPublicKeyDefault, WithNeitherDesignationWrittenNoneStands) {
  ReadUnderKeys run(ForeignEnvelope(NamesProvider(kProvider)),
                    ProtectKeyList());
  EXPECT_TRUE(run.Designated().value.empty());
}

TEST(ProtectDigestPublicKeyEncryptionOutput, TheDesignationIsWrittenOut) {
  std::string designation =
      DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  std::string envelope = WrittenOutOf(Region(designation));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find(designation), std::string::npos) << envelope;
}

TEST(ProtectDigestPublicKeyEncryptionOutput, ARegionDesignatingNoneGetsNone) {
  std::string envelope = WrittenOutOf(Region(NamesProvider(kProvider)));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_public_key"), std::string::npos) << envelope;
}

TEST(ProtectDigestPublicKeyEncryptionOutput, AnUnreadableLineDesignatesNone) {
  std::string envelope =
      WrittenOutOf(Region("`pragma protect digest_public_key\nnot a block\n"));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_public_key"), std::string::npos) << envelope;
}

}  // namespace
