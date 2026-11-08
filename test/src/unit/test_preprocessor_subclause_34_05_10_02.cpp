#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kOwner = "acme-semiconductor";

constexpr std::string_view kOtherOwner = "globex-ip";

constexpr std::string_view kSharedValue = "one-designation";

constexpr std::string_view kOtherValue = "another-designation";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

ProtectEncoding BlockEncoding() { return DefaultProtectEncoding(); }

std::string NamesKeyOwner(std::string_view owner) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  return text;
}

std::string NamesKeyName(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

std::string DesignatesPublicKey(std::string_view value) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(value, BlockEncoding())).append("\n");
  return text;
}

std::string DesignatesDecryptKey(std::string_view value) {
  std::string text = "`pragma protect data_decrypt_key\n";
  text.append(EncodeProtectBlock(value, BlockEncoding())).append("\n");
  return text;
}

std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

struct Read {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit Read(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Reported(std::string_view message) const {
    for (const auto& d : diag.Diagnostics()) {
      if (d.message.find(message) != std::string::npos) return true;
    }
    return false;
  }
};

constexpr std::string_view kTwoNamesOneValue =
    "writes one value against two of the names that designate a key of the "
    "data_keyowner in effect";

TEST(ProtectDataKeyownerDescription, PublicKeyRepeatingTheKeyNameIsReported) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesPublicKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(), kTwoNamesOneValue, 5, "34.5.10"));
}

TEST(ProtectDataKeyownerDescription, DecryptKeyRepeatingTheKeyNameIsReported) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesDecryptKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(), kTwoNamesOneValue, 5, "34.5.10"));
}

TEST(ProtectDataKeyownerDescription,
     OneValueUnderTwoEntitiesIsTwoDesignations) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += NamesKeyOwner(kOtherOwner);
  described += DesignatesPublicKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

TEST(ProtectDataKeyownerDescription, DistinctValuesUnderOneEntityAreLeftAlone) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesPublicKey(kOtherValue);
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

TEST(ProtectDataKeyownerDescription, TwoEmptyDesignationsRepeatNothing) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName("");
  described += DesignatesPublicKey("");
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

TEST(ProtectDataKeyownerDescription,
     TheEntityGoesOutInTheSpellingItCameInWith) {
  std::string region = "`pragma protect begin\n";
  region += "`pragma protect data_keyowner=acme_semiconductor\n";
  region.append(kSealedDesign);
  region += "`pragma protect end\n";
  std::string envelope = EncryptEnvelopes(region, "one-key-of-the-authors-own");
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("data_keyowner=acme_semiconductor"),
            std::string::npos)
      << envelope;
}

constexpr std::string_view kBlockProvider = "meridian-trust";
constexpr std::string_view kBlockProviderName = "wrapping-2029";
constexpr std::string_view kBlockProviderKey = "meridian-trust-wrapping-key";

constexpr std::string_view kDataProvider = "kestrel-systems";
constexpr std::string_view kDataProviderName = "kestrel-data-2029";
constexpr std::string_view kDataProviderKey = "kestrel-region-exchange-key";

constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

std::string DesignatesTheBlocksKey() {
  std::string text = "`pragma protect key_keyowner=\"";
  text.append(kBlockProvider).append("\"\n");
  text += "`pragma protect key_keyname=\"";
  text.append(kBlockProviderName).append("\"\n");
  return text;
}

std::string RegionNamingBothProviders() {
  std::string text = "`pragma protect begin\n";
  text.append(NamesKeyOwner(kDataProvider));
  text.append(NamesKeyName(kDataProviderName));
  text.append(DesignatesTheBlocksKey());
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

std::string RegionNamingTheDataProviderAlone() {
  std::string text = "`pragma protect begin\n";
  text.append(NamesKeyOwner(kDataProvider));
  text.append(NamesKeyName(kDataProviderName));
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

ProtectKeyList OnlyTheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  return keys;
}

ProtectKeyList BothProvidersKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  keys.Add(KeyOf(kDataProvider, kDataProviderName, kDataProviderKey));
  return keys;
}

TEST(ProtectDataKeyownerEncryptionOutput,
     TheEntityLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, "data_keyowner")) << envelope;
}

TEST(ProtectDataKeyownerEncryptionOutput,
     TheEntityStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingTheDataProviderAlone(),
                                          {}, BothProvidersKeys());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesKeyOwner(kDataProvider))) << envelope;
}

TEST(ProtectDataKeyownerEncryptionOutput,
     TheEntityInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheBlockProvidersKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
}

TEST(ProtectDataKeyownerEncryptionInput, OneValueAgainstTwoNamesIsReported) {
  std::string src = "`pragma protect begin\n";
  src.append("`pragma protect data_keyowner=\"acme\"\n");
  src.append("`pragma protect data_keyname=\"same-value\"\n");
  src.append("`pragma protect data_public_key\n");
  src.append(EncodeProtectValue("same-value", DefaultProtectEncoding()));
  src.append("\nmodule sealed_m; endmodule\n`pragma protect end\n");
  SourceManager mgr;
  DiagEngine diag(mgr);
  EncryptEnvelopes(src, "exchange", ProtectKeyList(), &diag,
                   mgr.AddFile("<test>", src));
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "protect pragma writes one value against two of "
                            "the names that designate a key of the "
                            "data_keyowner in effect",
                            1, "34.5.10"));
}

TEST(ProtectDataKeyownerEncryptionInput, DistinctValuesAreNotReported) {
  std::string src = "`pragma protect begin\n";
  src.append("`pragma protect data_keyowner=\"acme\"\n");
  src.append("`pragma protect data_keyname=\"one-value\"\n");
  src.append("`pragma protect data_public_key\n");
  src.append(EncodeProtectValue("another-value", DefaultProtectEncoding()));
  src.append("\nmodule sealed_m; endmodule\n`pragma protect end\n");
  SourceManager mgr;
  DiagEngine diag(mgr);
  EncryptEnvelopes(src, "exchange", ProtectKeyList(), &diag,
                   mgr.AddFile("<test>", src));
  EXPECT_FALSE(ReportedError(diag.Diagnostics(),
                             "protect pragma writes one value against two of "
                             "the names that designate a key of the "
                             "data_keyowner in effect",
                             1, "34.5.10"));
}

}  // namespace
