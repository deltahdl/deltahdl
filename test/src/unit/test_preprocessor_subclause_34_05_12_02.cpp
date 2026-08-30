// §34.5.12.2 data_keyname, Description.
//
// The subclause says three things about the keyword §34.5.12.1 spells.
//
//   Written in an encrypting tool's input, it names the key -- or the key pair,
//   where the algorithm is asymmetric -- that the data_block is to be decrypted
//   with. It shall be an error to name a key that is not a member of the list
//   of keys known for the data_keyowner given.
//
//   The name is output as cleartext in the output file, except where a digital
//   envelope is used, in which case it is encrypted under the key_method and
//   the key the key_keyname or key_public_key designates, and encoded in the
//   key_block.
//
//   Read in a protected envelope, the name is combined with the data_keyowner
//   to select the single key the data_block is decrypted with.
//
// The first is the rule with teeth and it is what this file leads with: a name
// outside the entity's list is reported where it is written, by
// Preprocessor::CheckDataKeyname
// (src/preprocessor/preprocessor_protect_keynames.cpp). The entity is what the
// list belongs to, so the same name is inside one entity's list and outside
// another's, and a tool holding no list for the entity has none for the name to
// be absent from.
//
// The third is what makes the first matter, and it is observed the way a
// reading observes it: a region sealed under a key is opened again only where
// the pair of names an envelope carries reaches that key.
//
// The second is AppendClearDataNames in
// src/preprocessor/protect_envelope_output.cpp, and the exception it states is
// covered here too. §34.5.27.2 has an encrypting tool form a key block when it
// is requested to use a digital signature, so an envelope carrying a key block
// is the digital envelope the exception names, and the name is absent from
// everything a reader can read without opening that block. The envelope of a
// region whose name reached a key of the author's carries no key block, and
// states the name in the clear. The last case reads the excepted envelope back,
// so the name is shown relocated rather than dropped. Issue #3268 is the
// defect: the name stood in the clear whether the envelope carried key blocks
// or not.
//
// A fourth claim follows from the spelling §34.5.12.1 gives the expression,
// `data_keyname = <string>`. §22.5.1 makes a parenthesized pragma_value a list
// of further expressions rather than one written thing, so a list written
// against the keyword names no key. The last three cases read what the tool
// wrote rather than what a Preprocessor holds: a list leaves the envelope with
// no data_keyname directive at all, a string in the same place puts one there,
// and a list written after a string leaves the earlier name standing. Issue
// #3273 is the defect: the list was taken as the name and written into the
// envelope quoted, which is no pragma_expression §22.11 admits.

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

// The entity whose list of keys a name is looked for in, and a second entity
// holding a key of its own under a name the first one does not hold. With one
// entity in the tool's hands a reading that never looked at the entity would
// answer the same as one that did.
constexpr std::string_view kOwner = "acme-semiconductor";
constexpr std::string_view kOtherOwner = "globex-ip";

// The name each of them holds a key under, and the keys those pairs reach.
constexpr std::string_view kOwnerKeyName = "acme-2026";
constexpr std::string_view kOtherKeyName = "globex-2026";
constexpr std::string_view kOwnerKey = "acme-region-exchange-key";
constexpr std::string_view kOtherKey = "globex-region-exchange-key";

// The design a region seals.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The report a name outside its entity's list draws.
constexpr std::string_view kNoSuchKey =
    "data_keyname names no key held by the data_keyowner in effect";

// A user holding one key of each party, each under its own name.
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

// The two directives §34.5.10.1 and §34.5.12.1 designate a key with.
std::string Names(std::string_view owner, std::string_view keyname) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  text += "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

// One encryption envelope with `described` and then the design between the
// words §34.5.1.1 and §34.5.2.1 define.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

// §34.5.12.2: it shall be an error to name a key that is not a member of the
// list of keys known for the entity given. The entity here holds one key and
// the region names another, so the name reaches nothing.
TEST(ProtectDataKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Names(kOwner, "a-key-nobody-holds");
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "data_keyname"), "34.5.12"));
}

// §34.5.12.2: the list is the one known for the entity given, so a name one
// entity holds a key under is outside another's list. This is the same name
// that passes under its own entity in the case below, so what is reported is
// the pairing rather than the name.
TEST(ProtectDataKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Names(kOwner, kOtherKeyName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "data_keyname"), "34.5.12"));
}

// §34.5.12.2: a name that is a member of the entity's list is what the rule
// admits, so nothing is reported. Without this the two cases above would hold
// of an implementation reporting every name it was given.
TEST(ProtectDataKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Names(kOwner, kOwnerKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.12.2: the same name under the entity that does hold a key by it. The
// two entities and the two names are the same four values as the case that was
// reported, differently paired, so the entity is shown to decide which list the
// name is looked for in.
TEST(ProtectDataKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Names(kOtherOwner, kOtherKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.12.2: the rule is about a name absent from a list, so a tool holding no
// list for the entity named has none for the name to be absent from and reports
// nothing. A reading that reported here would refuse every name whenever it
// held no keys at all.
TEST(ProtectDataKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Names("a-party-nobody-holds-keys-for", kOwnerKeyName), f,
             HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.12.2: read in a protected envelope, the name is combined with the
// entity to select the single key the data block is decrypted with. The region
// is sealed under the key that pair reaches and the same pair opens it again.
TEST(ProtectDataKeynameDescription, ThePairSelectsTheKeyTheBlockIsOpenedWith) {
  std::string envelope = EncryptEnvelopes(Region(Names(kOwner, kOwnerKeyName)),
                                          "", KeysOfBothParties());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

// §34.5.12.2: the name is output as cleartext, no digital envelope being in
// use here, so the pair the reading needs stands in the envelope where a reader
// can find it rather than inside the block it opens.
TEST(ProtectDataKeynameDescription, TheNameStandsInTheEnvelopeAsCleartext) {
  std::string envelope = EncryptEnvelopes(Region(Names(kOwner, kOwnerKeyName)),
                                          "", KeysOfBothParties());
  EXPECT_NE(envelope.find(kOwnerKeyName), std::string::npos) << envelope;
}

// ---------------------------------------------------------------------------
// The name travels in a key block where a digital envelope is used.
// ---------------------------------------------------------------------------

// The entity that provided the key a region's own keys travel under, with the
// name picking that key out of its list and the key itself. §34.5.27.2 forms a
// key block for a region designating one, and that block is where §34.5.12.2
// sends the name of the key the data are under.
constexpr std::string_view kBlockProvider = "aegis-custody";
constexpr std::string_view kBlockProviderName = "wrapping-2031";
constexpr std::string_view kBlockProviderKey = "aegis-custody-wrapping-key";

// The expression announcing a key block, which is how a case below tells an
// envelope carrying one from an envelope that carries none.
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

// The directive §34.5.12.1 names the key the data are under with, on its own.
// Names above writes it beside the entity §34.5.10.1 names, and what the cases
// below ask is whether this one line reaches the envelope.
std::string NamesTheDataKey(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

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
  return Region(Names(kOwner, kOwnerKeyName) + DesignatesTheBlocksKey());
}

// The block provider's key alone. The region's data name reaches none of these,
// so the region is sealed behind the key block §34.5.27.2 writes.
ProtectKeyList OnlyTheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  return keys;
}

// That key beside the one the region's data name reaches. The region is now
// sealed under the second, and no key block is written at all.
ProtectKeyList TheDataKeyAsWell() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  keys.Add(KeyOf(kOwner, kOwnerKeyName, kOwnerKey));
  return keys;
}

// §34.5.12.2: the name is output as cleartext in the output file, except where
// a digital envelope is used, in which case it is encrypted using the
// key_method and the key the key_keyname or key_public_key designates, and
// encoded in the key_block. §34.5.27.2 forms a key block on a request for a
// digital signature, so this envelope is the excepted one, and the name stands
// nowhere a reader holding no key can read it.
//
// What the name is inside the block cannot be asserted here. The block is
// encrypted and then encoded, so its characters say nothing about what went
// into it, and the case reading the envelope back is what shows the name
// arrived.
TEST(ProtectDataKeynameEncryptionOutput,
     TheNameLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), "",
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, "data_keyname")) << envelope;
}

// §34.5.12.2 excepts the digital envelope and nothing else, so an envelope
// carrying no key block states the name in the clear. The source text is the
// text the case above encrypted, character for character; what differs is that
// the tool holds the key the name reaches, so the exception does not arise.
TEST(ProtectDataKeynameEncryptionOutput,
     TheNameStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope =
      EncryptEnvelopes(RegionNamingBothProviders(), "", TheDataKeyAsWell());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDataKey(kOwnerKeyName))) << envelope;
}

// The excepted envelope read back by the provider whose key opens its block.
// §34.5.12.2 relocates the name rather than discarding it, so the region still
// opens and the design comes back: an envelope that had dropped the name would
// pass the case above and fail here.
TEST(ProtectDataKeynameEncryptionOutput, TheNameInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), "",
                                          OnlyTheBlockProvidersKey());
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheBlockProvidersKey()));
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
}

// ---------------------------------------------------------------------------
// A parenthesized list against the keyword names no key.
// ---------------------------------------------------------------------------

// The key the three regions below are sealed under, supplied as the single key
// a user holds rather than through a list of them. §34.5.12.2 writes the name
// out whichever key the region went under, so supplying the key this way leaves
// what the name does the only thing these cases turn on.
constexpr std::string_view kSealingKey = "vault-region-exchange-key";

// The parenthesized pragma_value §22.5.1 defines: expressions between
// parentheses rather than one written thing. What stands inside is a keyword of
// somebody's own with a value against it, which is what such a list carries.
constexpr std::string_view kKeynameList =
    "(sealed_by=\"thales-hsm\", rotates=2031)";

// A name written the way §34.5.12.1 defines the expression, for the case that
// holds the region fixed and varies only the spelling of the value.
constexpr std::string_view kVaultedKeyName = "vault-2031";

// The characters an envelope writes ahead of this keyword's value. A case
// asking whether the envelope names a key at all searches for these, a list
// taken as the value having been written back quoted like any other value.
constexpr std::string_view kKeynameDirectiveHead = "data_keyname=\"";

// One protect pragma directive writing `value` against the keyword exactly as
// given, with no quotation marks of its own, so a parenthesized list reaches
// the reading as the list §22.5.1 defines rather than as a string that happens
// to hold parentheses.
std::string WritesTheDataKeyname(std::string_view value) {
  std::string text = "`pragma protect data_keyname=";
  text.append(value).append("\n");
  return text;
}

// §34.5.12.1 spells the expression `data_keyname = <string>`, and §22.5.1 makes
// a parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list names no key. §34.5.12.2 writes the name into the
// envelope in the clear, so a tool taking the list publishes it there as though
// it were the name of a key. Issue #3273 is that defect.
TEST(ProtectDataKeynameEncryptionOutput, AListWritesNoNameIntoTheEnvelope) {
  std::string envelope =
      EncryptEnvelopes(Region(WritesTheDataKeyname(kKeynameList)), kSealingKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeynameDirectiveHead), 0U) << envelope;
}

// The same region with the string §34.5.12.1 defines standing where the list
// stood. The name reaches the envelope, so the case above is about the list
// rather than about a tool that writes no name at all.
TEST(ProtectDataKeynameEncryptionOutput, AStringWritesItsNameIntoTheEnvelope) {
  std::string envelope =
      EncryptEnvelopes(Region(NamesTheDataKey(kVaultedKeyName)), kSealingKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDataKey(kVaultedKeyName))) << envelope;
}

// A list written after a string had already named the key. Naming no key is not
// naming an empty one, so the envelope carries the name the earlier string
// gave: an expression naming nothing has no standing to take a name away.
TEST(ProtectDataKeynameEncryptionOutput,
     AListLeavesTheNameTheEnvelopeCarriesStanding) {
  std::string described = NamesTheDataKey(kVaultedKeyName);
  described += WritesTheDataKeyname(kKeynameList);
  std::string envelope = EncryptEnvelopes(Region(described), kSealingKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeynameDirectiveHead), 1U) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDataKey(kVaultedKeyName))) << envelope;
}

// ---------------------------------------------------------------------------
// The rule an encrypting run makes.
// ---------------------------------------------------------------------------

// One encrypting run over `src`, with the reports it made kept beside the text
// it wrote out. The source is added to the manager so that a report stands at
// the line of it the author wrote the name on.
struct SealingRun {
  PreprocFixture f;
  std::string text;

  explicit SealingRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, KeysOfBothParties(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}
};

// §34.5.12.2 states the rule under ENCRYPTION INPUT, which is the tool being
// handed a text to seal, and until #3279 no encrypting run made the report:
// RunEnvelopeEncryption constructs no Preprocessor, so
// Preprocessor::CheckDataKeyname was never reached from that mode. What an
// author got was silence and a file, and the file carried the design in the
// clear, a region whose designations reach no key being returned exactly as it
// was written.
//
// The name stands on the third line, the region opening on the first and
// closing on the fifth, so a report placed at either delimiter fails this.
TEST(ProtectDataKeynameEncryptionInput,
     ANameOutsideTheListIsReportedWhenSealing) {
  SealingRun run(Region(Names(kOwner, kOtherKeyName)));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNoSuchKey, 3, "34.5.12"))
      << run.text;
}

// The consequence the report is instead of, stated once: the region comes back
// exactly as it was written, design and all.
TEST(ProtectDataKeynameEncryptionInput,
     ARegionReachingNoKeyComesBackAsWritten) {
  SealingRun run(Region(Names(kOwner, kOtherKeyName)));
  EXPECT_NE(run.text.find(kSealedDesign), std::string::npos) << run.text;
}

// The control: a name the entity does hold. Without it the case above would
// hold of a tool that reported every region it was handed.
TEST(ProtectDataKeynameEncryptionInput, ANameTheEntityHoldsIsSealedInSilence) {
  SealingRun run(Region(Names(kOwner, kOwnerKeyName)));
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.text.find(kSealedDesign), std::string::npos) << run.text;
}

// A name written under an entity the tool holds no list for. A name cannot be
// found missing from a list that was never supplied, so nothing is reported and
// the name stands. That reading is what Preprocessor::CheckDataKeyname already
// gave, and a report made where both modes reach it must leave it standing.
TEST(ProtectDataKeynameEncryptionInput,
     ANameUnderAnUnknownEntityIsNotReported) {
  SealingRun run(Region(Names("a-party-holding-nothing-here", kOwnerKeyName)));
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
}

}  // namespace
