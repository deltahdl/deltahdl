#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kProvider = "helios-trust";
constexpr std::string_view kOtherProvider = "borealis-labs";

constexpr std::string_view kProviderName = "helios-digest-2027";
constexpr std::string_view kOtherName = "borealis-digest-2027";
constexpr std::string_view kProviderKey = "helios-digest-signing-key";
constexpr std::string_view kOtherKey = "borealis-digest-signing-key";

constexpr std::string_view kDataParty = "kestrel-systems";
constexpr std::string_view kDataName = "kestrel-data-2027";
constexpr std::string_view kDataKey = "kestrel-region-exchange-key";

constexpr std::string_view kUnheld = "a-name-nobody-holds-a-key-under";

constexpr std::string_view kHiddenDesign = "module hidden_m; endmodule\n";

constexpr std::string_view kNoSuchKey =
    "digest_keyname names no key held by the digest_keyowner in effect";

std::string Written(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Designates(std::string_view provider, std::string_view name) {
  return Written("digest_keyowner", provider) + Written("digest_keyname", name);
}

ProtectKeyList KeysOfEveryParty() {
  ProtectKeyList keys;
  keys.Add({std::string(kProvider), std::string(kProviderName),
            std::string(kProviderKey)});
  keys.Add({std::string(kOtherProvider), std::string(kOtherName),
            std::string(kOtherKey)});
  keys.Add(
      {std::string(kDataParty), std::string(kDataName), std::string(kDataKey)});
  return keys;
}

PreprocConfig HoldingEveryList() {
  PreprocConfig config;
  config.protect_keys = KeysOfEveryParty();
  return config;
}

struct ReadingOf {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, HoldingEveryList()};

  explicit ReadingOf(const std::string& src) {
    pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue NameInEffect() const {
    return pp.ProtectKeywords().DigestKeynameInEffect();
  }

  std::string_view DigestKey() const { return pp.DigestKeyInEffect(); }
};

std::string Sealing(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kHiddenDesign);
  text += "`pragma protect end\n";
  return text;
}

std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

std::string WrittenOutOf(const std::string& src) {
  return EncryptEnvelopes(src, kDataKey);
}

TEST(ProtectDigestKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Designates(kProvider, kUnheld);
  PreprocFixture f;
  Preprocess(src, f, HoldingEveryList());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "digest_keyname"), "34.5.18"));
}

TEST(ProtectDigestKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Designates(kProvider, kOtherName);
  PreprocFixture f;
  Preprocess(src, f, HoldingEveryList());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "digest_keyname"), "34.5.18"));
}

TEST(ProtectDigestKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Designates(kProvider, kProviderName), f, HoldingEveryList());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDigestKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Designates(kOtherProvider, kOtherName), f, HoldingEveryList());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDigestKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Designates("a-party-nobody-holds-keys-for", kProviderName), f,
             HoldingEveryList());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDigestKeynameDefault, TheDataNameFillsThePlaceLeftEmpty) {
  ReadingOf run(Written("data_keyname", kDataName));
  EXPECT_EQ(run.NameInEffect().value, kDataName);
}

TEST(ProtectDigestKeynameDefault, ThePlaceFilledFromTheDataNameIsADefault) {
  ReadingOf run(Written("data_keyname", kDataName));
  EXPECT_TRUE(run.NameInEffect().defaulted);
}

TEST(ProtectDigestKeynameDefault, ANameSpecifiedForTheDigestIsNoDefault) {
  ReadingOf run(Written("data_keyname", kDataName) +
                Written("digest_keyname", kProviderName));
  EXPECT_FALSE(run.NameInEffect().defaulted);
}

TEST(ProtectDigestKeynameDefault, ANameSpecifiedForTheDigestIsWhatStands) {
  ReadingOf run(Written("data_keyname", kDataName) +
                Written("digest_keyname", kProviderName));
  EXPECT_EQ(run.NameInEffect().value, kProviderName);
}

TEST(ProtectDigestKeynameDefault, ALaterDataNameLeavesTheDigestsAlone) {
  ReadingOf run(Written("digest_keyname", kProviderName) +
                Written("data_keyname", kDataName));
  EXPECT_EQ(run.NameInEffect().value, kProviderName);
}

TEST(ProtectDigestKeynameDefault, TheNameFilledInIsTheOneCurrentlyInEffect) {
  ReadingOf run(Written("data_keyname", kProviderName) +
                Written("data_keyname", kDataName));
  EXPECT_EQ(run.NameInEffect().value, kDataName);
}

TEST(ProtectDigestKeynameDefault, TheKeywordWithNothingAgainstItSpecifiesNone) {
  ReadingOf run(Written("data_keyname", kDataName) +
                "`pragma protect digest_keyname\n");
  EXPECT_EQ(run.NameInEffect().value, kDataName);
}

TEST(ProtectDigestKeynameDefault, AnEmptyStringSpecifiesNone) {
  ReadingOf run(Written("data_keyname", kDataName) +
                Written("digest_keyname", ""));
  EXPECT_EQ(run.NameInEffect().value, kDataName);
  EXPECT_TRUE(run.NameInEffect().defaulted);
}

TEST(ProtectDigestKeynameDefault, WithNeitherNameWrittenNoNameStands) {
  ReadingOf run(Written("digest_keyowner", kProvider));
  EXPECT_TRUE(run.NameInEffect().value.empty());
}

TEST(ProtectDigestKeynameEncryptionOutput,
     TheNameStandsInTheEnvelopeAsWritten) {
  std::string described = Designates(kProvider, kProviderName);
  std::string envelope = WrittenOutOf(Sealing(described));
  EXPECT_EQ(envelope.find(kHiddenDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find(described), std::string::npos) << envelope;
}

TEST(ProtectDigestKeynameEncryptionOutput, ARegionThatSpecifiedNoneGetsNone) {
  std::string envelope = WrittenOutOf(Sealing(std::string()));
  EXPECT_EQ(envelope.find(kHiddenDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_keyname"), std::string::npos) << envelope;
}

TEST(ProtectDigestKeynameEncryptionOutput, AListPutsNoNameOnTheEnvelope) {
  std::string envelope = WrittenOutOf(
      Sealing("`pragma protect digest_keyname=(held_by=\"helios-trust\")\n"));
  EXPECT_EQ(envelope.find(kHiddenDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_keyname=\""), std::string::npos) << envelope;
}

TEST(ProtectDigestKeynameDecryptionInput, TheNameAndTheEntityReachOneKey) {
  ReadingOf run(EnvelopeCarrying(Designates(kProvider, kProviderName)));
  EXPECT_EQ(run.DigestKey(), kProviderKey);
}

TEST(ProtectDigestKeynameDecryptionInput, TheNameFilledInIsPairedTheSameWay) {
  std::string described = Written("digest_keyowner", kDataParty);
  described += Written("data_keyname", kDataName);
  ReadingOf run(EnvelopeCarrying(described));
  EXPECT_EQ(run.DigestKey(), kDataKey);
}

TEST(ProtectDigestKeynameDecryptionInput,
     ThatNameUnderAnotherPartyReachesNone) {
  ReadingOf run(EnvelopeCarrying(Designates(kOtherProvider, kProviderName)));
  EXPECT_TRUE(run.DigestKey().empty());
}

constexpr std::string_view kBlockProvider = "cerulean-vault";
constexpr std::string_view kBlockProviderName = "wrapping-2033";
constexpr std::string_view kBlockProviderKey = "cerulean-vault-wrapping-key";

constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

std::string RegionNamingBothProviders() {
  std::string described = Designates(kProvider, kProviderName);
  described += Written("data_keyowner", kDataParty);
  described += Written("data_keyname", kDataName);
  described += Written("key_keyowner", kBlockProvider);
  described += Written("key_keyname", kBlockProviderName);
  return Sealing(described);
}

std::string RegionNamingTheDataProviderAlone() {
  std::string described = Designates(kProvider, kProviderName);
  described += Written("data_keyowner", kDataParty);
  described += Written("data_keyname", kDataName);
  return Sealing(described);
}

ProtectKeyList OnlyTheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  return keys;
}

ProtectKeyList TheDataKeyAsWell() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  keys.Add(KeyOf(kDataParty, kDataName, kDataKey));
  return keys;
}

TEST(ProtectDigestKeynameEncryptionOutput,
     TheDigestNameLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kHiddenDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, "digest_keyname")) << envelope;
  EXPECT_TRUE(Holds(envelope, Written("digest_keyowner", kProvider)))
      << envelope;
}

TEST(ProtectDigestKeynameEncryptionOutput,
     TheDigestNameStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingTheDataProviderAlone(),
                                          {}, TheDataKeyAsWell());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kHiddenDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Written("digest_keyname", kProviderName)))
      << envelope;
}

TEST(ProtectDigestKeynameDecryptionInput,
     TheDigestNameInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheBlockProvidersKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kHiddenDesign)) << run.text;
}

struct DigestSealingRun {
  PreprocFixture f;
  std::string text;

  explicit DigestSealingRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, KeysOfEveryParty(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}
};

TEST(ProtectDigestKeynameEncryptionInput,
     AnUnheldDigestNameIsReportedWhenSealing) {
  DigestSealingRun run(Sealing(Designates(kProvider, kUnheld)));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNoSuchKey, 3, "34.5.18"))
      << run.text;
}

TEST(ProtectDigestKeynameEncryptionInput, AHeldDigestNameIsSealedInSilence) {
  DigestSealingRun run(Sealing(Designates(kProvider, kProviderName)));
  EXPECT_EQ(run.f.diag.ErrorCount(), 1U) << run.text;
  EXPECT_TRUE(
      ReportedError(run.f.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

TEST(ProtectDigestKeynameEncryptionInput, ANameFallsBackToTheDatasEntity) {
  std::string described = Written("data_keyowner", kDataParty);
  described += Written("digest_keyname", kDataName);
  DigestSealingRun run(Sealing(described));
  EXPECT_EQ(run.f.diag.ErrorCount(), 1U) << run.text;
  EXPECT_TRUE(
      ReportedError(run.f.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

}  // namespace
