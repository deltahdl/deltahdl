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
// (Preprocessor::TakeDataBlockValue,
// src/preprocessor/preprocessor_protect_values.cpp).
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
// The first and second of those are what the file closes with, read from the
// side that writes an envelope rather than the side that reads one.
// §34.5.11.2's ENCRYPTION INPUT states that the identifier "specifies the
// encryption algorithm that shall be used to encrypt subsequent begin-end
// blocks", so a region naming one has stated what its own block is to be
// produced with. This implementation provides one cipher and names it
// kDataMethod (src/preprocessor/protect_envelope_output.h), so a region naming
// any other identifier has asked for a block this tool cannot produce, and it
// is told so. Table 34-3 decides the second half of that report: des-cbc is the
// one identifier the table marks Required, and the other fifteen are Optional.
// Issue #3270 is the defect: the encrypting half read the keyword nowhere, so a
// region asking for des-cbc was sealed under this tool's stream cipher and its
// envelope claimed x-deltahdl-stream as though that was what had been asked
// for. Issue #3430 covers providing des-cbc, and the report is what stands in
// its place until that lands.
//
// Table 34-3 itself is modelled in src/preprocessor/protect_key_method.h, which
// §34.5.24 shares, so the identifiers written below are the tabulated spellings
// rather than spellings invented here.

#include <gtest/gtest.h>

#include <cstdint>
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

// The 1-based line of `envelope` its data block is written on, which is the
// line a report about that block stands at. §34.5.15.1 spells the announcing
// expression as the keyword standing alone and §34.5.15.2 has the block begin
// on the next line in the file, so the block is one line past that expression
// (issue #3272).
uint32_t TheCipheredBlocksLine(std::string_view envelope) {
  return LineHolding(envelope, "`pragma protect data_block\n") + 1;
}

// §34.5.11.2: the data_method states the algorithm the data block is decrypted
// with, and des-cbc is the identifier Table 34-3 requires of an implementation.
// This one does not provide it, so a block naming it is not opened and the
// reading says so rather than handing back what the tool's own cipher made of
// those bytes.
TEST(ProtectDataMethodDescription,
     ABlockNamingARequiredCipherWeLackIsReported) {
  ReadBack run(EnvelopeNaming("des-cbc"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            TheCipheredBlocksLine(run.source), "34.5.11.2"))
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
                            TheCipheredBlocksLine(run.source), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: further identifiers are implementation-defined, and one this tool
// does not know names a cipher it cannot read with all the same.
TEST(ProtectDataMethodDescription, ABlockNamingAnUnknownIdentifierIsReported) {
  ReadBack run(EnvelopeNaming("x-some-other-tools-cipher"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            TheCipheredBlocksLine(run.source), "34.5.11.2"))
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
// this shows: Preprocessor::TakeDataBlockValue
// (src/preprocessor/preprocessor_protect_values.cpp) reads it out of the scope
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

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the cipher a region asks its own block to be made with.
// ---------------------------------------------------------------------------

// The design the regions below seal, and the key they are sealed under.
constexpr std::string_view kAskedDesign = "module gasket_m; endmodule\n";
constexpr std::string_view kAskingKey = "another-key-of-the-authors-own";

// The design sealed by the one region below that asks for no cipher at all. It
// is spelled apart from the design above so that a case reading an output for
// it is reading for the text of its own region.
constexpr std::string_view kUnaskedDesign = "module cradle_m; endmodule\n";

// The report a region asking for a cipher this implementation does not produce
// draws, up to the identifier that region named.
constexpr std::string_view kNoSuchCipher =
    "asks for an encryption algorithm this implementation does not provide: ";

// The two halves of Table 34-3, as that report names them. Which half a report
// carries is what separates an identifier the standard obliges every
// implementation to provide from an identifier it leaves optional.
constexpr std::string_view kTableRequires =
    ", which IEEE 1800-2023 Table 34-3 requires of every implementation";
constexpr std::string_view kTableAdmitsWithoutRequiring =
    ", which IEEE 1800-2023 Table 34-3 does not require of every "
    "implementation";

// The whole of that report for one identifier drawn from one half of the table.
std::string AsksFor(std::string_view identifier, std::string_view tabulated) {
  std::string message(kNoSuchCipher);
  message.append(identifier).append(tabulated);
  return message;
}

// Envelope encryption over a source text an author wrote, with the reports the
// reading made kept beside the text it produced. The source is added to the
// manager so that a report stands at the line of it the author wrote the
// identifier on, that line being what the cases below name.
struct SealingRun {
  PreprocFixture f;
  std::string text;

  explicit SealingRun(const std::string& src)
      : text(EncryptEnvelopes(src, kAskingKey, ProtectKeyList(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}

  // Whether the region holding `design` came back as a block rather than as
  // the characters the author wrote.
  bool Sealed(std::string_view design) const {
    return !Holds(text, design) && Holds(text, kDataBlockKeyword);
  }
};

// §34.5.11.2: the identifier states "the encryption algorithm that shall be
// used to encrypt subsequent begin-end blocks", so a region naming des-cbc has
// stated what its own block is to be produced with. This implementation
// produces one cipher and des-cbc is not it. Table 34-3 marks des-cbc Required,
// and the report says so, because §34.5.11.2 calls a required method "standard
// in every implementation" and this implementation is the one falling short.
// Issue #3430 covers providing the cipher, and this report is what stands in
// its place until that lands. Issue #3270 is the defect the case was written
// for: the encrypting half read the keyword nowhere, so this region was sealed
// under the tool's own cipher and its envelope claimed x-deltahdl-stream as
// though that was what the author had asked for.
//
// The identifier stands on the second line and the region closes on the fourth,
// so a report placed where the region closes fails this.
TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForTheRequiredCipherIsReported) {
  std::string src = "`pragma protect begin\n";
  src.append(Writes(kDataMethodKeyword, "des-cbc"));
  src.append(kAskedDesign);
  src += "`pragma protect end\n";
  SealingRun run(src);
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            AsksFor("des-cbc", kTableRequires), 2, "34.5.11.2"))
      << run.text;
}

// §34.5.11.2: Table 34-3 marks aes256-cbc Optional, and the report says that
// instead. An implementation offering that cipher is required to offer it under
// this identifier, and this one offers it under no identifier at all. The half
// of the table the identifier came from is the whole of what separates this
// case from the one above, so the message is read for that half.
//
// The identifier stands on the third line here rather than the second, the
// region opening inside a design element.
TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForAnOptionalCipherSaysTheTableDoesNotRequireIt) {
  std::string src = "module bezel_m;\n`pragma protect begin\n";
  src.append(Writes(kDataMethodKeyword, "aes256-cbc"));
  src += "  initial hatch = 7;\n`pragma protect end\nendmodule\n";
  SealingRun run(src);
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            AsksFor("aes256-cbc", kTableAdmitsWithoutRequiring),
                            3, "34.5.11.2"))
      << run.text;
}

// §34.5.11.2: a region asking for the cipher this implementation does produce
// is refused nothing, so it is sealed and no report is made. kDataMethod
// (src/preprocessor/protect_envelope_output.h) is that identifier, and
// §34.5.11.2 leaves an identifier outside Table 34-3 to the implementation that
// coins it. Without this case the two above would hold of a tool that reported
// every region whatever cipher it asked for.
TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForTheCipherWeProvideIsSealedInSilence) {
  std::string src = "`pragma protect begin\n";
  src.append(StatesTheCipherWeProvide());
  src.append(kAskedDesign);
  src += "`pragma protect end\n";
  SealingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Sealed(kAskedDesign)) << run.text;
}

// §34.5.11.2 governs a region that named an algorithm, and a region naming none
// asked for nothing that could be refused. Such a region is sealed under this
// implementation's own cipher and the reading says nothing about it. Without
// this case the two reported ones would hold of a tool that objected to every
// region it read, the identifier notwithstanding.
TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForNoCipherIsSealedInSilence) {
  std::string src = "`pragma protect begin\n";
  src.append(kUnaskedDesign);
  src += "`pragma protect end\n";
  SealingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Sealed(kUnaskedDesign)) << run.text;
}

// §34.4 makes the scope of a protect pragma keyword lexical, so an identifier
// written ahead of a region is in effect inside that region and states what its
// block is to be produced with. The report therefore stands on the line the
// author wrote the identifier on, which is the first, and not on either
// delimiter of the region, which are the third and the fifth. blowfish-cbc is
// one of Table 34-3's optional identifiers.
TEST(ProtectDataMethodEncryptionInput,
     ACipherNamedAheadOfTheRegionIsReportedOnItsOwnLine) {
  std::string src = Writes(kDataMethodKeyword, "blowfish-cbc");
  src += "module bracket_m; endmodule\n`pragma protect begin\n";
  src += "  initial latch = 3;\n`pragma protect end\n";
  SealingRun run(src);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      AsksFor("blowfish-cbc", kTableAdmitsWithoutRequiring), 1, "34.5.11.2"))
      << run.text;
}

}  // namespace
