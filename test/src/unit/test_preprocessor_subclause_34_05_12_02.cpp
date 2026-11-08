#include <gtest/gtest.h>

#include <string>
#include <string_view>

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

constexpr std::string_view kOwner = "acme-semiconductor";
constexpr std::string_view kOtherOwner = "globex-ip";

constexpr std::string_view kOwnerKeyName = "acme-2026";
constexpr std::string_view kOtherKeyName = "globex-2026";
constexpr std::string_view kOwnerKey = "acme-region-exchange-key";
constexpr std::string_view kOtherKey = "globex-region-exchange-key";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kNoSuchKey =
    "data_keyname names no key held by the data_keyowner in effect";

ProtectKeyList KeysOfBothParties() {
  ProtectKeyList keys;
  keys.Add({std::string(kOwner), std::string(kOwnerKeyName),
            std::string(kOwnerKey)});
  keys.Add({std::string(kOtherOwner), std::string(kOtherKeyName),
            std::string(kOtherKey)});
  return keys;
}

PreprocConfig HoldingBothLists() {
  PreprocConfig config;
  config.protect_keys = KeysOfBothParties();
  return config;
}

std::string Names(std::string_view owner, std::string_view keyname) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  text += "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

TEST(ProtectDataKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Names(kOwner, "a-key-nobody-holds");
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "data_keyname"), "34.5.12"));
}

TEST(ProtectDataKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Names(kOwner, kOtherKeyName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "data_keyname"), "34.5.12"));
}

TEST(ProtectDataKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Names(kOwner, kOwnerKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDataKeynameDescription, TheKeywordStandingAloneNamesNoKey) {
  std::string src = "`pragma protect data_keyowner=\"";
  src.append(kOwner).append("\"\n`pragma protect data_keyname\n");
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDataKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Names(kOtherOwner, kOtherKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDataKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Names("a-party-nobody-holds-keys-for", kOwnerKeyName), f,
             HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectDataKeynameDescription, ThePairSelectsTheKeyTheBlockIsOpenedWith) {
  std::string envelope = EncryptEnvelopes(Region(Names(kOwner, kOwnerKeyName)),
                                          "", KeysOfBothParties());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

TEST(ProtectDataKeynameDescription, TheNameStandsInTheEnvelopeAsCleartext) {
  std::string envelope = EncryptEnvelopes(Region(Names(kOwner, kOwnerKeyName)),
                                          "", KeysOfBothParties());
  EXPECT_NE(envelope.find(kOwnerKeyName), std::string::npos) << envelope;
}

constexpr std::string_view kBlockProvider = "aegis-custody";
constexpr std::string_view kBlockProviderName = "wrapping-2031";
constexpr std::string_view kBlockProviderKey = "aegis-custody-wrapping-key";

constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

std::string NamesTheDataKey(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

std::string DesignatesTheBlocksKey() {
  std::string text = "`pragma protect key_keyowner=\"";
  text.append(kBlockProvider).append("\"\n");
  text += "`pragma protect key_keyname=\"";
  text.append(kBlockProviderName).append("\"\n");
  return text;
}

std::string RegionNamingBothProviders() {
  return Region(Names(kOwner, kOwnerKeyName) + DesignatesTheBlocksKey());
}

std::string RegionNamingTheDataProviderAlone() {
  return Region(Names(kOwner, kOwnerKeyName));
}

ProtectKeyList OnlyTheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  return keys;
}

ProtectKeyList TheDataKeyAsWell() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  keys.Add(KeyOf(kOwner, kOwnerKeyName, kOwnerKey));
  return keys;
}

TEST(ProtectDataKeynameEncryptionOutput,
     TheNameLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), "",
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, "data_keyname")) << envelope;
}

TEST(ProtectDataKeynameEncryptionOutput,
     TheNameStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingTheDataProviderAlone(),
                                          "", TheDataKeyAsWell());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDataKey(kOwnerKeyName))) << envelope;
}

TEST(ProtectDataKeynameEncryptionOutput, TheNameInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), "",
                                          OnlyTheBlockProvidersKey());
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheBlockProvidersKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
}

constexpr std::string_view kSealingKey = "vault-region-exchange-key";

constexpr std::string_view kKeynameList =
    "(sealed_by=\"thales-hsm\", rotates=2031)";

constexpr std::string_view kVaultedKeyName = "vault-2031";

constexpr std::string_view kKeynameDirectiveHead = "data_keyname=\"";

std::string WritesTheDataKeyname(std::string_view value) {
  std::string text = "`pragma protect data_keyname=";
  text.append(value).append("\n");
  return text;
}

TEST(ProtectDataKeynameEncryptionOutput, AListWritesNoNameIntoTheEnvelope) {
  std::string envelope =
      EncryptEnvelopes(Region(WritesTheDataKeyname(kKeynameList)), kSealingKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeynameDirectiveHead), 0U) << envelope;
}

TEST(ProtectDataKeynameEncryptionOutput, AStringWritesItsNameIntoTheEnvelope) {
  std::string envelope =
      EncryptEnvelopes(Region(NamesTheDataKey(kVaultedKeyName)), kSealingKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDataKey(kVaultedKeyName))) << envelope;
}

TEST(ProtectDataKeynameEncryptionOutput,
     AListLeavesTheNameTheEnvelopeCarriesStanding) {
  std::string described = NamesTheDataKey(kVaultedKeyName);
  described += WritesTheDataKeyname(kKeynameList);
  std::string envelope = EncryptEnvelopes(Region(described), kSealingKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeynameDirectiveHead), 1U) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDataKey(kVaultedKeyName))) << envelope;
}

struct SealingRun {
  PreprocFixture f;
  std::string text;

  explicit SealingRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, KeysOfBothParties(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}
};

TEST(ProtectDataKeynameEncryptionInput,
     ANameOutsideTheListIsReportedWhenSealing) {
  SealingRun run(Region(Names(kOwner, kOtherKeyName)));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNoSuchKey, 3, "34.5.12"))
      << run.text;
}

TEST(ProtectDataKeynameEncryptionInput,
     ARegionReachingNoKeyComesBackAsWritten) {
  SealingRun run(Region(Names(kOwner, kOtherKeyName)));
  EXPECT_NE(run.text.find(kSealedDesign), std::string::npos) << run.text;
  EXPECT_TRUE(
      ReportedError(run.f.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            "protect pragma data_keyname names no key held by "
                            "the data_keyowner in effect",
                            3, "34.5.12"));
}

TEST(ProtectDataKeynameEncryptionInput, ANameTheEntityHoldsIsSealedInSilence) {
  SealingRun run(Region(Names(kOwner, kOwnerKeyName)));
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.text.find(kSealedDesign), std::string::npos) << run.text;
}

TEST(ProtectDataKeynameEncryptionInput,
     ANameUnderAnUnknownEntityIsNotReported) {
  SealingRun run(Region(Names("a-party-holding-nothing-here", kOwnerKeyName)));
  EXPECT_EQ(run.f.diag.ErrorCount(), 1U) << run.text;
  EXPECT_TRUE(
      ReportedError(run.f.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

}  // namespace
