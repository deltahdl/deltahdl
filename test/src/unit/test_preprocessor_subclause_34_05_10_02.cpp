// §34.5.10.2 data_keyowner, Description.
//
// The subclause says four things about the keyword §34.5.10.1 spells.
//
//   It names the legal entity or tool that provided the keys used to encrypt
//   and decrypt the data, and it permits a third-party key, distinct from one
//   associated with either author or encrypt_agent.
//
//   An encrypting tool uses its value to select the key that encrypts the
//   data_block.
//
//   The values written against data_keyname, data_decrypt_key and
//   data_public_key are unique for the entity it names.
//
//   It is unchanged in the output file, except where a digital signature is
//   used, in which case it is encrypted with the key_method and placed in a
//   key_block.
//
// The syntax file beside this one covers what spellings the keyword admits and
// which of them reaches a key. What is left here are the two rules that speak
// about the values around it: the uniqueness of the three designations for one
// entity, and the value going out as it came in.
//
// Both are preprocessor-stage rules. The uniqueness one is
// Preprocessor::CheckDataKeyDesignationValue
// (src/preprocessor/preprocessor_protect_keynames.cpp), reached from the
// expression-shaped designation §34.5.12.1 writes and from the two §34.5.13.1
// and §34.5.14.1 write as a keyword standing alone with the value on the line
// beneath it; the output one is ProtectDataKeyownerDirective
// (src/preprocessor/protect_keywords.cpp), which the envelope writer calls.
//
// The three designations are spelled here as their own subclauses spell them,
// so a value reaching the rule reaches it the way a source text sends it and
// not through the one spelling that happens to be easiest to write.
//
// The exception that rule states is covered here as well. §34.5.27.2 has an
// encrypting tool form a key block when it is requested to use a digital
// signature, so an envelope carrying a key block is the excepted case, and the
// entity is absent from everything a reader can read without opening that
// block. The envelope of a region whose data name reached a key of the author's
// carries no key block, and states the entity in the clear. The last case reads
// the excepted envelope back, so the entity is shown relocated rather than
// dropped. Issue #3268 is the defect: the entity stood in the clear whether the
// envelope carried key blocks or not.

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

// The entity whose keys the designations below pick among.
constexpr std::string_view kOwner = "acme-semiconductor";

// A second entity. One value is unique for the entity it is written under, so
// the same characters under two entities are two designations rather than one
// repeated, and this is what that claim is made with.
constexpr std::string_view kOtherOwner = "globex-ip";

// The value written against two of the three designating names, which is what
// the rule forbids for one entity.
constexpr std::string_view kSharedValue = "one-designation";

// A second value, for the pair that designates two keys rather than one twice.
constexpr std::string_view kOtherValue = "another-designation";

// The design a region seals, for the output rule below.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

ProtectEncoding BlockEncoding() { return DefaultProtectEncoding(); }

// The directive §34.5.10.1 names the entity with.
std::string NamesKeyOwner(std::string_view owner) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  return text;
}

// The directive §34.5.12.1 names one of that entity's keys with. This is the
// designation written against its keyword.
std::string NamesKeyName(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

// The two lines §34.5.13.1 spells a public key over: the keyword standing
// alone, and the encoded value on the line beneath it.
std::string DesignatesPublicKey(std::string_view value) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(value, BlockEncoding())).append("\n");
  return text;
}

// The two lines §34.5.14.1 spells a decryption key over, in the same shape.
std::string DesignatesDecryptKey(std::string_view value) {
  std::string text = "`pragma protect data_decrypt_key\n";
  text.append(EncodeProtectBlock(value, BlockEncoding())).append("\n");
  return text;
}

// A decryption envelope as another tool wrote it. The two designations spelled
// as a keyword standing alone are read only inside one, an announcement outside
// every envelope being text of the design rather than a value.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// A reading of `src`, with the diagnostics it raised kept.
struct Read {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit Read(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // Whether the reading reported anything carrying `message`. The cases that
  // expect nothing name the message they expect nothing of, so a run reporting
  // something else entirely does not read as the rule holding.
  bool Reported(std::string_view message) const {
    for (const auto& d : diag.Diagnostics()) {
      if (d.message.find(message) != std::string::npos) return true;
    }
    return false;
  }
};

// The message the uniqueness rule reports with.
constexpr std::string_view kTwoNamesOneValue =
    "writes one value against two of the names that designate a key of the "
    "data_keyowner in effect";

// §34.5.10.2: the values written against data_keyname, data_decrypt_key and
// data_public_key are unique for the entity named. The key name and the public
// key here carry one value under one entity, so that value would have to
// designate two of the entity's keys at once. §34.5.13.1 writes the public key
// as a keyword standing alone with its value beneath it, which is the spelling
// a rule reading only the value written against a keyword never sees.
TEST(ProtectDataKeyownerDescription, PublicKeyRepeatingTheKeyNameIsReported) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesPublicKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  // The report stands at the line the announced value is on, which is the line
  // the designation is read from, rather than at the keyword announcing it.
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(), kTwoNamesOneValue, 5, "34.5.10"));
}

// §34.5.10.2: the same of the third designating name. §34.5.14.1 spells the
// decryption key the way §34.5.13.1 spells the public key, so it reaches the
// rule by its own path and neither case stands for the other.
TEST(ProtectDataKeyownerDescription, DecryptKeyRepeatingTheKeyNameIsReported) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesDecryptKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  // The report stands at the line the announced value is on, which is the line
  // the designation is read from, rather than at the keyword announcing it.
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(), kTwoNamesOneValue, 5, "34.5.10"));
}

// §34.5.10.2: the values are unique for the entity specified, so two entities
// each designating a key by the same characters designate two keys. Reporting
// this would make the rule one about the characters rather than about the
// entity they are unique for.
TEST(ProtectDataKeyownerDescription,
     OneValueUnderTwoEntitiesIsTwoDesignations) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += NamesKeyOwner(kOtherOwner);
  described += DesignatesPublicKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

// §34.5.10.2: two designating names carrying different values under one entity
// pick out two of that entity's keys, which is what the names are for. Without
// this the cases above would hold of an implementation reporting every second
// designation an entity writes.
TEST(ProtectDataKeyownerDescription, DistinctValuesUnderOneEntityAreLeftAlone) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesPublicKey(kOtherValue);
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

// §34.5.10.2: the data_keyowner is unchanged in the output file. §22.5.1 admits
// a bare identifier as a pragma_value, so an entity named with one is named
// with those characters; writing it back as a string would change the value the
// source wrote. No digital signature is in play here, which is the one case the
// subclause excepts.
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

// ---------------------------------------------------------------------------
// The entity travels in a key block where a digital signature is used.
// ---------------------------------------------------------------------------

// The entity that provided the key a region's own keys travel under, with the
// name picking that key out of its list and the key itself. §34.5.27.2 forms a
// key block for a region designating one, and that block is where §34.5.10.2
// sends the entity named for the data.
constexpr std::string_view kBlockProvider = "meridian-trust";
constexpr std::string_view kBlockProviderName = "wrapping-2029";
constexpr std::string_view kBlockProviderKey = "meridian-trust-wrapping-key";

// The entity a region names for its data, with the name picking a key out of
// its list and the key itself.
constexpr std::string_view kDataProvider = "kestrel-systems";
constexpr std::string_view kDataProviderName = "kestrel-data-2029";
constexpr std::string_view kDataProviderKey = "kestrel-region-exchange-key";

// The expression announcing a key block, which is how a case below tells an
// envelope carrying one from an envelope that carries none.
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

// The two directives §34.5.23.1 and §34.5.25.1 designate the key a region's own
// keys travel under with.
std::string DesignatesTheBlocksKey() {
  std::string text = "`pragma protect key_keyowner=\"";
  text.append(kBlockProvider).append("\"\n");
  text += "`pragma protect key_keyname=\"";
  text.append(kBlockProviderName).append("\"\n");
  return text;
}

// The region every case below encrypts. It names an entity and a key for its
// data and designates a provider for its own keys, so the text says nothing
// about which of the two arrangements it gets: what decides is whether the tool
// holds the key the data name reaches.
std::string RegionNamingBothProviders() {
  std::string text = "`pragma protect begin\n";
  text.append(NamesKeyOwner(kDataProvider));
  text.append(NamesKeyName(kDataProviderName));
  text.append(DesignatesTheBlocksKey());
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

// The block provider's key alone. The region's data name reaches none of these,
// so the region is sealed behind the key block §34.5.27.2 writes.
ProtectKeyList OnlyTheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  return keys;
}

// Both keys. The region's data name now reaches one, so the region is sealed
// under it and no key block is written at all.
ProtectKeyList BothProvidersKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  keys.Add(KeyOf(kDataProvider, kDataProviderName, kDataProviderKey));
  return keys;
}

// §34.5.10.2: the entity is unchanged in the output file, except where a
// digital signature is used, in which case it is encrypted with the key_method
// and placed in a key_block. §34.5.27.2 forms a key block on a request for a
// digital signature, so this envelope is the excepted one, and the entity
// stands nowhere a reader holding no key can read it.
//
// What the entity is inside the block cannot be asserted here. The block is
// encrypted and then encoded, so its characters say nothing about what went
// into it, and the case reading the envelope back is what shows the entity
// arrived.
TEST(ProtectDataKeyownerEncryptionOutput,
     TheEntityLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, "data_keyowner")) << envelope;
}

// §34.5.10.2 excepts the digital signature and nothing else, so an envelope
// carrying no key block states the entity in the clear. The source text is the
// text the case above encrypted, character for character; what differs is that
// the tool holds the key the region's data name reaches, so the exception does
// not arise.
TEST(ProtectDataKeyownerEncryptionOutput,
     TheEntityStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope =
      EncryptEnvelopes(RegionNamingBothProviders(), {}, BothProvidersKeys());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesKeyOwner(kDataProvider))) << envelope;
}

// The excepted envelope read back by the provider whose key opens its block.
// §34.5.10.2 relocates the entity rather than discarding it, so the region
// still opens and the design comes back: an envelope that had dropped the
// entity would pass the case above and fail here.
TEST(ProtectDataKeyownerEncryptionOutput,
     TheEntityInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheBlockProvidersKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
}

}  // namespace
