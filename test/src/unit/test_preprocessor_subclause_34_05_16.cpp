#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kDataOwner = "acme";

constexpr std::string_view kDigestOwner = "veritas-signing";

constexpr std::string_view kBareDigestOwner = "veritas_signing";

constexpr std::string_view kOtherOwner = "globex";

constexpr std::string_view kDigestKeyName = "digest-2026";
constexpr std::string_view kDigestKey = "veritas-digest-signing-key";

constexpr std::string_view kDigestPublicKey = "veritas-rsa-public-key";

constexpr std::string_view kUnheldKeyName = "no-key-of-theirs";

constexpr std::string_view kSharedValue = "one-value-in-two-places";

constexpr std::string_view kDataKeyName = "data-2026";
constexpr std::string_view kDataKey = "acme-region-exchange-key";

constexpr std::string_view kKeyProvider = "aegis-custody";
constexpr std::string_view kKeyProviderKeyName = "wrapping-2026";
constexpr std::string_view kKeyProviderKey = "aegis-custody-wrapping-key";

constexpr std::string_view kNumericOwner = "1997";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Region(const std::string& described, std::string_view body) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(body);
  text.append("`pragma protect end\n");
  return text;
}

std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

ProtectKeyList KeyHeldUnder(std::string_view owner,
                            std::string_view designation,
                            std::string_view key = kDigestKey) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(designation), std::string(key)});
  return keys;
}

ProtectKeyList KeysForDataAndDigest() {
  ProtectKeyList keys;
  keys.Add({std::string(kDataOwner), std::string(kDataKeyName),
            std::string(kDataKey)});
  keys.Add({std::string(kDigestOwner), std::string(kDigestKeyName),
            std::string(kDigestKey)});
  return keys;
}

ProtectKeyList KeysBothUnderTheDataParty() {
  ProtectKeyList keys;
  keys.Add({std::string(kDataOwner), std::string(kDataKeyName),
            std::string(kDataKey)});
  keys.Add({std::string(kDataOwner), std::string(kDigestKeyName),
            std::string(kDigestKey)});
  return keys;
}

PreprocConfig KeysConfig(const ProtectKeyList& keys) {
  PreprocConfig config;
  config.protect_keys = keys;
  return config;
}

struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys)
      : pp(mgr, diag, KeysConfig(keys)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  std::string_view DigestKey() const { return pp.DigestKeyInEffect(); }

  std::string_view DigestBlockKey() const {
    return pp.DigestBlockKeyInEffect();
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

std::string EncryptedUnderNames(const std::string& src,
                                const ProtectKeyList& keys) {
  return EncryptEnvelopes(src, "", keys);
}

std::string RequestsDigest() { return "`pragma protect digest_block\n"; }

std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kDataKey);
}

size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + needle.size());
  }
  return count;
}

TEST(ProtectDigestKeyownerExpression,
     TheStringAgainstTheKeywordNamesTheEntity) {
  ReadUnderKeys run(Writes("digest_keyowner", kDigestOwner), ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kDigestOwner);
}

TEST(ProtectDigestKeyownerExpression, ABareIdentifierNamesTheEntityItSpells) {
  ReadUnderKeys run("`pragma protect digest_keyowner=veritas_signing\n",
                    ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kBareDigestOwner);
}

TEST(ProtectDigestKeyownerExpression, TheKeywordStandsInAListOfExpressions) {
  ReadUnderKeys run(
      "`pragma protect data_method=\"des-cbc\", digest_keyowner=\"acme\"\n",
      ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kDataOwner);
}

TEST(ProtectDigestKeyownerExpression, ANumberIsAValueLikeTheOtherTwo) {
  ReadUnderKeys run("`pragma protect digest_keyowner=1997\n", ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kNumericOwner);
}

TEST(ProtectDigestKeyownerExpression, ANameOneLetterOffNamesNoEntity) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyownr", kOtherOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDefault,
     TheDataProviderStandsWhereTheDigestNamedNone) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDefault,
     ANamedEntityIsNotDisplacedByTheDataProvider) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyowner", kOtherOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(run.DigestKey().empty());
}

TEST(ProtectDigestKeyownerDefault,
     TheKeywordWithNothingAgainstItNamesNoEntity) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += "`pragma protect digest_keyowner\n";
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDefault, TheEntityFilledInIsTheOneCurrentlyInEffect) {
  std::string src = Writes("data_keyowner", kOtherOwner);
  src += Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDefault, WithNeitherNameWrittenNoEntityStands) {
  ReadUnderKeys run(Writes("digest_keyname", kDigestKeyName),
                    KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_TRUE(run.DigestKey().empty());
}

TEST(ProtectDigestKeynameUnderDefaultedEntity, ANameOutsideThatListIsReported) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kUnheldKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma digest_keyname names no key held "
                            "by the digest_keyowner in effect",
                            2, "34.5.18"));
}

TEST(ProtectDigestDesignationUniqueness, OneValueAgainstTwoNamesIsReported) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

TEST(ProtectDigestDesignationUniqueness, TheSessionKeyIsHeldToTheSameRule) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_decrypt_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

TEST(ProtectDigestDesignationUniqueness, TwoEntitiesMakeTwoDesignations) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_keyowner", kOtherOwner);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectDigestDesignationUniqueness, ANameRewrittenWithItsOwnValueStands) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_keyname", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectDigestDesignationUniqueness,
     TheDefaultedEntityIsWhatTheyAreUniqueFor) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("data_keyowner", kOtherOwner);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectDigestDesignationUniqueness, OneDefaultedEntityMakesOneRepetition) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

TEST(ProtectDigestDesignationUniqueness, TheSessionKeyAndThePublicKeyPairToo) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_decrypt_key", kSharedValue);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

TEST(ProtectDigestDesignationUniqueness, ADataNameIsOutsideTheThree) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("data_keyname", kSharedValue);
  src += Writes("digest_keyname", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectDigestKeyownerEncryptionOutput, TheNameIsWrittenIntoTheEnvelope) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(described), std::string::npos);
}

TEST(ProtectDigestKeyownerEncryptionOutput,
     TheSpellingComesBackAsItWasWritten) {
  std::string described = "`pragma protect digest_keyowner=veritas_signing\n";
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_NE(encrypted.find(described), std::string::npos);
  EXPECT_EQ(encrypted.find("digest_keyowner=\""), std::string::npos);
}

TEST(ProtectDigestKeyownerEncryptionOutput, ARegionThatNamedNoneGetsNone) {
  std::string encrypted = Encrypted(Region(std::string(), kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("digest_keyowner"), std::string::npos);
}

TEST(ProtectDigestKeyownerEncryptionOutput, ANameAheadOfTheRegionStandsTwice) {
  std::string named = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted =
      Encrypted(named + Region(std::string(), kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, named), 2U);
  EXPECT_LT(encrypted.find(named),
            encrypted.find("`pragma protect begin_protected\n"));
}

TEST(ProtectDigestKeyownerEncryptionOutput,
     TheEntityStandsAheadOfTheNameAndTheBlock) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_NE(encrypted.find(described), std::string::npos);
  EXPECT_LT(encrypted.find(described), encrypted.find("data_block"));
}

TEST(ProtectDigestKeyownerEncryptionOutput, AnEnvelopeCarryingKeysStatesItToo) {
  std::string described = Writes("key_keyowner", kKeyProvider);
  described += Writes("key_keyname", kKeyProviderKeyName);
  std::string named = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted = EncryptedUnderNames(
      Region(described + named, kSealedDesign),
      KeyHeldUnder(kKeyProvider, kKeyProviderKeyName, kKeyProviderKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect key_block"), std::string::npos);
  EXPECT_NE(encrypted.find(named), std::string::npos);
}

TEST(ProtectDigestKeyownerDecryptionInput, TheEntityAndTheKeyNameReachOneKey) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDecryptionInput,
     ThatNameUnderAnotherEntityReachesNone) {
  std::string described = Writes("digest_keyowner", kOtherOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_TRUE(run.DigestKey().empty());
}

TEST(ProtectDigestKeyownerDecryptionInput,
     TheEntityAndThePublicKeyReachOneKey) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_public_key", kDigestPublicKey);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestPublicKey));
  EXPECT_EQ(run.DigestBlockKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDecryptionInput,
     ThePublicKeyRouteTakesTheDefaultToo) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("digest_public_key", kDigestPublicKey);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDataOwner, kDigestPublicKey));
  EXPECT_EQ(run.DigestBlockKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerDecryptionInput,
     ThatPublicKeyUnderAnotherEntityReachesNone) {
  std::string described = Writes("digest_keyowner", kOtherOwner);
  described += Writes("digest_public_key", kDigestPublicKey);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestPublicKey));
  EXPECT_TRUE(run.DigestBlockKey().empty());
}

TEST(ProtectDigestKeyownerDecryptionInput,
     ANameMissingFromThatEntitysListIsReported) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kUnheldKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma digest_keyname names no key held "
                            "by the digest_keyowner in effect",
                            3, "34.5.18"));
  EXPECT_TRUE(run.DigestKey().empty());
}

TEST(ProtectDigestKeyownerDecryptionInput,
     TheEntityNeedBeNeitherOfTheOtherTwo) {
  std::string described = Writes("author", kDataOwner);
  described += Writes("encrypt_agent", kOtherOwner);
  described += Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

TEST(ProtectDigestKeyownerEncryptionInput, TheEntityNamedSelectsTheDigestKey) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  described += Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysForDataAndDigest());
  ReadUnderKeys run(encrypted, KeysForDataAndDigest());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestKeyownerEncryptionInput, ARegionNamingNoneKeepsTheDataKey) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysForDataAndDigest());
  ReadUnderKeys run(encrypted, KeysForDataAndDigest());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestKeyownerEncryptionInput, AnEmptyStringNamesNoPartyEither) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  described += Writes("digest_keyowner", "");
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysBothUnderTheDataParty());
  ReadUnderKeys run(encrypted, KeysBothUnderTheDataParty());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestKeyownerEncryptionInput, AnEntityWithNoKeysSelectsNothing) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  described += Writes("digest_keyowner", kOtherOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysForDataAndDigest());
  ReadUnderKeys run(encrypted, KeysForDataAndDigest());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

std::string Announces(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("\n");
  text.append(EncodeProtectBlock(value, DefaultProtectEncoding())).append("\n");
  return text;
}

TEST(ProtectDigestDesignationUniqueness, AnAnnouncedPublicKeyIsHeldToTheRule) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kSharedValue);
  described += Announces("digest_public_key", kSharedValue);
  std::string src = ForeignEnvelope(described);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      LineHolding(src, EncodeProtectBlock(std::string(kSharedValue),
                                          DefaultProtectEncoding())),
      "34.5.16"));
}

TEST(ProtectDigestDesignationUniqueness, AnAnnouncedSessionKeyIsHeldToTheRule) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kSharedValue);
  described += Announces("digest_decrypt_key", kSharedValue);
  std::string src = ForeignEnvelope(described);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      LineHolding(src, EncodeProtectBlock(std::string(kSharedValue),
                                          DefaultProtectEncoding())),
      "34.5.16"));
}

constexpr std::string_view kEntityList = "(division=\"notary\", desk=\"emea\")";

constexpr std::string_view kEntityDirectiveHead = "digest_keyowner=";

std::string WritesUnquoted(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=").append(value).append("\n");
  return text;
}

TEST(ProtectDigestKeyownerEncryptionOutput, AListPutsNoEntityIntoTheEnvelope) {
  std::string encrypted = Encrypted(
      Region(WritesUnquoted("digest_keyowner", kEntityList), kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, kEntityDirectiveHead), 0U);
}

TEST(ProtectDigestKeyownerEncryptionOutput,
     AStringPutsItsEntityIntoTheEnvelope) {
  std::string named = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted = Encrypted(Region(named, kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, named), 1U);
}

TEST(ProtectDigestKeyownerEncryptionOutput,
     AListLeavesTheEntityTheEnvelopeCarriesStanding) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += WritesUnquoted("digest_keyowner", kEntityList);
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, kEntityDirectiveHead), 1U);
  EXPECT_NE(encrypted.find(Writes("digest_keyowner", kDigestOwner)),
            std::string::npos);
}

}  // namespace
