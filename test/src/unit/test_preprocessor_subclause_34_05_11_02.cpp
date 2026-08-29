// §34.5.11.2 data_method, Description.
//
// The subclause says four things about the keyword §34.5.11.1 spells.
//
//   Written in an encrypting tool's input, it states the encryption algorithm
//   that shall be used to encrypt the begin-end blocks that follow it, named by
//   an identifier commonly associated with a specific cipher.
//
//   Table 34-3 lists the identifiers the standard settles. des-cbc is required
//   of every implementation; the rest are optional, an implementation offering
//   one of those ciphers is required to offer it under the tabulated name, and
//   further identifiers and their ciphers are implementation-defined.
//
//   The data_method is unchanged in the output file, except where a digital
//   signature is used, in which case it is encrypted with the key_method and
//   placed in a key_block.
//
//   Read in a protected envelope, it states the algorithm the data_block is to
//   be decrypted with.
//
// The last of those is what this file opens with, and it is the one an
// implementation offering a single cipher has to answer for. This tool provides
// one, states its own implementation-defined identifier for it in every
// envelope it writes, and cannot read a block written under any other. Reading
// such a block under the cipher it does provide would hand back whatever those
// bytes became rather than the design, so the identifier the envelope states is
// checked before the block is opened
// (Preprocessor::DecryptDataBlock,
// src/preprocessor/preprocessor_protect_keys.cpp).
//
// The third of those is covered here as well, and it is the one an envelope
// carrying key blocks answers differently. §34.5.11.2 excepts a single case
// from the identifier standing unchanged: "except where a digital signature is
// used, in which case it is encrypted with the key_method and placed in a
// key_block". §34.5.27.2 has an encrypting tool form a key block when it is
// requested to use a digital signature, so an envelope carrying one is the
// excepted case, and the identifier is absent from everything a reader holding
// no key can read. The envelope of a region whose data name reached a key the
// tool holds carries no key block, and states the identifier in the clear. The
// last case reads the excepted envelope back, so the identifier is shown
// relocated rather than dropped. Issue #3428 is the defect: the identifier
// stood in the clear whether the envelope carried key blocks or not.
//
// Table 34-3 itself is modelled in src/preprocessor/protect_key_method.h, which
// §34.5.24 shares, so the identifiers written below are the tabulated spellings
// rather than spellings invented here.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The design a region seals, and the key it is sealed under.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kRegionKey = "one-key-of-the-authors-own";

// The report a block naming an algorithm this implementation does not provide
// draws.
constexpr std::string_view kNotProvided =
    "states an encryption algorithm this implementation does not provide";

// An envelope this tool wrote for a region holding the sealed design, which
// states the tool's own identifier and carries a block it can open.
std::string OurEnvelope() {
  std::string region = "`pragma protect begin\n";
  region.append(kSealedDesign);
  region += "`pragma protect end\n";
  std::string envelope = EncryptEnvelopes(region, std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

// The same envelope with the algorithm it states replaced by `identifier`,
// which is how a block written under some other tool's cipher reaches a
// reading. Only the stated identifier changes; the block is left as it was, so
// what a case observes is the identifier deciding whether the block is opened.
std::string EnvelopeNaming(std::string_view identifier) {
  std::string envelope = OurEnvelope();
  std::string ours = "`pragma protect data_method=\"";
  ours.append(kDataMethod).append("\"");
  auto at = envelope.find(ours);
  EXPECT_NE(at, std::string::npos) << envelope;
  if (at == std::string::npos) return envelope;
  std::string theirs = "`pragma protect data_method=\"";
  theirs.append(identifier).append("\"");
  return envelope.replace(at, ours.size(), theirs);
}

// A reading of `src` by a tool holding the key the region was sealed under.
struct ReadBack {
  PreprocFixture f;
  std::string source;
  std::string text;

  explicit ReadBack(const std::string& src) : source(src) {
    PreprocConfig config;
    config.protect_key = std::string(kRegionKey);
    text = Preprocess(src, f, config);
  }

  bool Recovered() const {
    return text.find(kSealedDesign) != std::string::npos;
  }
};

// §34.5.11.2: the data_method states the algorithm the data block is decrypted
// with, and des-cbc is the identifier Table 34-3 requires of an implementation.
// This one does not provide it, so a block naming it is not opened and the
// reading says so rather than handing back what the tool's own cipher made of
// those bytes.
TEST(ProtectDataMethodDescription,
     ABlockNamingARequiredCipherWeLackIsReported) {
  ReadBack run(EnvelopeNaming("des-cbc"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            LineHolding(run.source, "data_block"), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: the same of one of Table 34-3's optional identifiers. An
// implementation offering that cipher would have to offer it under this name,
// and this one does not offer it at all.
TEST(ProtectDataMethodDescription,
     ABlockNamingAnOptionalCipherWeLackIsReported) {
  ReadBack run(EnvelopeNaming("aes128-cbc"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            LineHolding(run.source, "data_block"), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: further identifiers are implementation-defined, and one this tool
// does not know names a cipher it cannot read with all the same.
TEST(ProtectDataMethodDescription, ABlockNamingAnUnknownIdentifierIsReported) {
  ReadBack run(EnvelopeNaming("x-some-other-tools-cipher"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            LineHolding(run.source, "data_block"), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: the identifier decides whether the block is read, so a block
// naming the algorithm this tool does provide is read. Without this the three
// cases above would hold of an implementation that refused every block.
TEST(ProtectDataMethodDescription, ABlockNamingTheCipherWeProvideIsRead) {
  ReadBack run(OurEnvelope());
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_TRUE(run.Recovered()) << run.text;
}

// ---------------------------------------------------------------------------
// The identifier travels in a key block where a digital signature is used.
// ---------------------------------------------------------------------------

// The entity that provided the key a region's own keys travel under, with the
// name picking that key out of its list and the key itself. §34.5.27.2 forms a
// key block for a region designating one, and that block is where §34.5.11.2
// sends the identifier naming the cipher the region's data are under.
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

// The directive an envelope states the cipher with, up to the value. What the
// signed case claims is that no such directive is written at all, so the value
// is left out of what it searches for.
constexpr std::string_view kMethodDirective = "`pragma protect data_method=";

// One directive carrying one keyword and the string that keyword records.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The directive an envelope states the cipher its data block is under with,
// carrying this tool's own identifier for the one cipher it provides.
std::string StatesTheCipherWeProvide() {
  return Writes(kDataMethodKeyword, kDataMethod);
}

// The region every case below encrypts. It names an entity and a key for its
// data and designates a provider for its own keys, so the text says nothing
// about which of the two arrangements it gets: what decides is whether the tool
// holds the key the data name reaches.
std::string RegionNamingBothProviders() {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kDataProvider));
  text.append(Writes("data_keyname", kDataProviderName));
  text.append(Writes("key_keyowner", kBlockProvider));
  text.append(Writes("key_keyname", kBlockProviderName));
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

// §34.5.11.2: the identifier is unchanged in the output file, except where a
// digital signature is used, in which case it is encrypted with the key_method
// and placed in a key_block. §34.5.27.2 forms a key block on a request for a
// digital signature, so this envelope is the excepted one, and the identifier
// stands nowhere a reader holding no key can read it.
//
// The count of key blocks is asserted first. Without it an envelope that was
// never written at all would satisfy the claim about the identifier, there
// being no envelope for the identifier to stand in.
//
// What the identifier is inside the block cannot be asserted here. The block is
// encrypted and then encoded, so its characters say nothing about what went
// into it, and the case reading the envelope back is what shows the identifier
// arrived. test_preprocessor_subclause_34_05_27_02.cpp holds the helper that
// decodes and decrypts a block, and its case
// ProtectKeyBlockDescription.TheBufferCarriesWhatOpensTheDataBlock reads the
// identifier out of the recovered buffer directly.
TEST(ProtectDataMethodEncryptionOutput,
     TheCipherLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, kMethodDirective)) << envelope;
}

// §34.5.11.2 excepts the digital signature and nothing else, so an envelope
// carrying no key block states the identifier in the clear. The source text is
// the text the case above encrypted, character for character; what differs is
// that the tool holds the key the region's data name reaches, so the exception
// does not arise.
TEST(ProtectDataMethodEncryptionOutput,
     TheCipherStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope =
      EncryptEnvelopes(RegionNamingBothProviders(), {}, BothProvidersKeys());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, StatesTheCipherWeProvide())) << envelope;
}

// The excepted envelope read back by the provider whose key opens its block.
// §34.5.11.2 relocates the identifier rather than discarding it, so the region
// still opens and the design comes back. That the identifier arrived is what
// this shows: Preprocessor::DecryptDataBlock
// (src/preprocessor/preprocessor_protect_keys.cpp) reads it out of the scope
// the recovered key block wrote, and it stands there under no other writing,
// the envelope having stated none in the clear.
TEST(ProtectDataMethodEncryptionOutput,
     TheCipherInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  PreprocFixture f;
  PreprocConfig config;
  config.protect_keys = OnlyTheBlockProvidersKey();
  std::string read = Preprocess(envelope, f, config);
  EXPECT_FALSE(f.diag.HasErrors()) << read;
  EXPECT_TRUE(Holds(read, kSealedDesign)) << read;
}

}  // namespace
