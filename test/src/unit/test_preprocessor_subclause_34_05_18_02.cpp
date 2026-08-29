// §34.5.18.2 digest_keyname, Description.
//
// The subclause says four things about the keyword §34.5.18.1 spells.
//
//   Written in an encrypting tool's input, it names the key -- or the key pair,
//   where the algorithm is asymmetric -- that the digest_block is to be
//   decrypted with. It shall be an error to name a key that is not a member of
//   the list of keys known for the digest_keyowner given.
//
//   Where an input names no key for its digest, the name in effect is the one
//   the region's data carry. A design whose digest is under the same key as its
//   data says so by saying nothing.
//
//   The name is output as cleartext in the output file, except where a digital
//   envelope is used, in which case it travels inside the key_block encrypted
//   under the key_method and the key that key_keyname or key_public_key
//   designates.
//
//   Read in a protected envelope, the name is combined with the digest_keyowner
//   to select the single key the digest_block is decrypted with.
//
// The first is the rule with teeth: a name outside the entity's list is
// reported where it is written, by Preprocessor::CheckDigestKeyname in
// src/preprocessor/preprocessor_protect_keynames.cpp. The entity is what the
// list belongs to, so one name is inside one entity's list and outside
// another's, and a tool holding no list for the entity has none for the name to
// be absent from.
//
// The second is ProtectKeywordScope::DigestKeynameInEffect in
// src/preprocessor/protect_keywords.cpp, and it turns on whether a name was
// specified rather than on whether the keyword was mentioned.
//
// The third is AppendClearDigestNames in
// src/preprocessor/protect_envelope_output.cpp and the reading that carries the
// name onto an envelope, TakeKeyDesignations in
// src/preprocessor/protect_region_lines.cpp. §34.5.27.2 has an encrypting tool
// form a key block when it is requested to use a digital signature, so an
// envelope carrying a key block is the digital envelope the exception names,
// and the name is absent from everything a reader can read without opening that
// block. The envelope of a region whose data name reached a key of the author's
// carries no key block, and states the name in the clear. One case reads the
// excepted envelope back, so the name is shown relocated rather than dropped.
// Issue #3268 is the defect: the name stood in the clear whether the envelope
// carried key blocks or not.
//
// The fourth is ProtectDigestKey in src/preprocessor/protect_keywords.cpp,
// reached through Preprocessor::DigestKeyInEffect, and it is what makes the
// first matter: a digest sealed under a key is opened again only where the pair
// of names an envelope carries reaches that key.

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

// The entity that provided the key a region's digest is under, and a second
// entity holding a key of its own under a name the first one does not hold.
// With one entity in the tool's hands a reading that never looked at the entity
// would answer the same as one that did.
constexpr std::string_view kProvider = "helios-trust";
constexpr std::string_view kOtherProvider = "borealis-labs";

// The name each of them holds a digest key under, and the keys those pairs
// reach.
constexpr std::string_view kProviderName = "helios-digest-2027";
constexpr std::string_view kOtherName = "borealis-digest-2027";
constexpr std::string_view kProviderKey = "helios-digest-signing-key";
constexpr std::string_view kOtherKey = "borealis-digest-signing-key";

// The entity whose key a region's data are under, the name it holds that key
// under, and the key itself. They are a fourth party and a fourth key, so a
// digest opened under the data's key did not open under the digest's own.
constexpr std::string_view kDataParty = "kestrel-systems";
constexpr std::string_view kDataName = "kestrel-data-2027";
constexpr std::string_view kDataKey = "kestrel-region-exchange-key";

// A name no entity below holds a key under.
constexpr std::string_view kUnheld = "a-name-nobody-holds-a-key-under";

// The design a region seals. Nothing of it survives the writing of an encrypted
// block, so finding it in what a tool wrote is finding a region that was never
// encrypted.
constexpr std::string_view kHiddenDesign = "module hidden_m; endmodule\n";

// The report a name outside its entity's list draws.
constexpr std::string_view kNoSuchKey =
    "digest_keyname names no key held by the digest_keyowner in effect";

// One protect pragma directive writing `value` against `keyword` as a string,
// which is the spelling §34.5.18.1 defines its own keyword in.
std::string Written(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The two directives §34.5.16.1 and §34.5.18.1 designate a digest's key with.
std::string Designates(std::string_view provider, std::string_view name) {
  return Written("digest_keyowner", provider) + Written("digest_keyname", name);
}

// A user holding one digest key of each provider and the key a region's data
// are under, each under its own name.
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

// A reading of `src` by a tool holding every party's list, with the
// preprocessor kept alive afterwards. What §34.5.18.2 leaves behind is the name
// standing in the digest's place and the key it reaches with the entity beside
// it, and both belong to the point the reading has got to rather than to any
// one directive.
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

// One encryption envelope: the words §34.5.1.1 and §34.5.2.1 define with
// `described` and then the design between them.
std::string Sealing(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kHiddenDesign);
  text += "`pragma protect end\n";
  return text;
}

// A decryption envelope as some other tool wrote it, carrying `described` and
// no block: the rules read through it are about which key a digest block would
// be opened with rather than about opening one.
std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

// What a tool wrote where the encryption envelopes of `src` stood, for an
// author who supplied one key of their own.
std::string WrittenOutOf(const std::string& src) {
  return EncryptEnvelopes(src, kDataKey);
}

// ---------------------------------------------------------------------------
// A name outside the entity's list is an error.
// ---------------------------------------------------------------------------

// §34.5.18.2: it shall be an error to name a key that is not a member of the
// list of keys known for the entity given. The entity here holds one digest key
// and the text names another, so the name reaches nothing.
TEST(ProtectDigestKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Designates(kProvider, kUnheld);
  PreprocFixture f;
  Preprocess(src, f, HoldingEveryList());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "digest_keyname"), "34.5.18"));
}

// §34.5.18.2: the list is the one known for the entity given, so a name one
// entity holds a key under is outside another's. This is the same name that
// passes under its own entity below, so what is reported is the pairing rather
// than the name.
TEST(ProtectDigestKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Designates(kProvider, kOtherName);
  PreprocFixture f;
  Preprocess(src, f, HoldingEveryList());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "digest_keyname"), "34.5.18"));
}

// §34.5.18.2: a name that is a member of the entity's list is what the rule
// admits, so nothing is reported. Without this the two cases above would hold
// of an implementation that reported every name it was given.
TEST(ProtectDigestKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Designates(kProvider, kProviderName), f, HoldingEveryList());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.18.2: the same name under the entity that does hold a key by it. The
// two entities and the two names are the four values the reported case used,
// differently paired, so the entity decides which list the name is looked for
// in.
TEST(ProtectDigestKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Designates(kOtherProvider, kOtherName), f, HoldingEveryList());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.18.2: the rule is about a name absent from a list, so a tool holding no
// list for the entity named has none for the name to be absent from and reports
// nothing. A reading that reported here would refuse every name whenever it
// held no keys of that party at all.
TEST(ProtectDigestKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Designates("a-party-nobody-holds-keys-for", kProviderName), f,
             HoldingEveryList());
  EXPECT_FALSE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// Where no name was specified, the data's name stands in its place.
// ---------------------------------------------------------------------------

// §34.5.18.2: the default value is the current value of data_keyname. This text
// names a key for its data and none for its digest, so the digest's place holds
// the data's name.
TEST(ProtectDigestKeynameDefault, TheDataNameFillsThePlaceLeftEmpty) {
  ReadingOf run(Written("data_keyname", kDataName));
  EXPECT_EQ(run.NameInEffect().value, kDataName);
}

// The same reading, on where that value came from. A default rule put it there
// rather than a directive naming a key for the digest, and a case reading only
// the characters cannot tell the two apart.
TEST(ProtectDigestKeynameDefault, ThePlaceFilledFromTheDataNameIsADefault) {
  ReadingOf run(Written("data_keyname", kDataName));
  EXPECT_TRUE(run.NameInEffect().defaulted);
}

// The negative: a text that named a key for its digest is under that name, and
// it is not a default. Without this the two cases above would hold of a reading
// that answered with the data's name whatever the digest said.
TEST(ProtectDigestKeynameDefault, ANameSpecifiedForTheDigestIsNoDefault) {
  ReadingOf run(Written("data_keyname", kDataName) +
                Written("digest_keyname", kProviderName));
  EXPECT_FALSE(run.NameInEffect().defaulted);
}

// The value that name leaves in effect, read beside the case above: the
// digest's own name rather than the data's, though both were written.
TEST(ProtectDigestKeynameDefault, ANameSpecifiedForTheDigestIsWhatStands) {
  ReadingOf run(Written("data_keyname", kDataName) +
                Written("digest_keyname", kProviderName));
  EXPECT_EQ(run.NameInEffect().value, kProviderName);
}

// The default fills an empty place and does not take a filled one. A data name
// written after the digest's own leaves the digest's where it was, or a text
// naming both keys would have its digest read under the data's key.
TEST(ProtectDigestKeynameDefault, ALaterDataNameLeavesTheDigestsAlone) {
  ReadingOf run(Written("digest_keyname", kProviderName) +
                Written("data_keyname", kDataName));
  EXPECT_EQ(run.NameInEffect().value, kProviderName);
}

// "Current" is what the text has in effect where the reading stands, §34.4
// making the scope of these values lexical. A text that named one key for its
// data and then another fills the digest's place from the second.
TEST(ProtectDigestKeynameDefault, TheNameFilledInIsTheOneCurrentlyInEffect) {
  ReadingOf run(Written("data_keyname", kProviderName) +
                Written("data_keyname", kDataName));
  EXPECT_EQ(run.NameInEffect().value, kDataName);
}

// What decides between the two is whether a name was specified, not whether the
// keyword was mentioned. A directive writing the keyword with nothing against
// it specified no key any more than leaving it out did.
TEST(ProtectDigestKeynameDefault, TheKeywordWithNothingAgainstItSpecifiesNone) {
  ReadingOf run(Written("data_keyname", kDataName) +
                "`pragma protect digest_keyname\n");
  EXPECT_EQ(run.NameInEffect().value, kDataName);
}

// A text that named no key anywhere has nothing for the default to fill the
// place from, so no name stands for its digest at all. That is a different
// state from a name that reaches none of the keys held, and it is what makes
// the cases above about the data's name rather than about any name at all.
TEST(ProtectDigestKeynameDefault, WithNeitherNameWrittenNoNameStands) {
  ReadingOf run(Written("digest_keyowner", kProvider));
  EXPECT_TRUE(run.NameInEffect().value.empty());
}

// ---------------------------------------------------------------------------
// The name is written out as cleartext.
// ---------------------------------------------------------------------------

// §34.5.18.2: the name is output as cleartext in the output file. The design it
// was written beside is gone, so the text holding the name is an envelope
// rather than a region that was never encrypted.
TEST(ProtectDigestKeynameEncryptionOutput,
     TheNameStandsInTheEnvelopeAsWritten) {
  std::string described = Designates(kProvider, kProviderName);
  std::string envelope = WrittenOutOf(Sealing(described));
  EXPECT_EQ(envelope.find(kHiddenDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find(described), std::string::npos) << envelope;
}

// The negative: a region that named no key for its digest has none named for
// it. A tool writing one there would state a key the input never specified,
// and a reader would then combine it with the entity beside it.
TEST(ProtectDigestKeynameEncryptionOutput, ARegionThatSpecifiedNoneGetsNone) {
  std::string envelope = WrittenOutOf(Sealing(std::string()));
  EXPECT_EQ(envelope.find(kHiddenDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_keyname"), std::string::npos) << envelope;
}

// §34.5.18.1 defines the expression with a string, so a parenthesized list of
// further expressions names no key, and a region writing one specified none for
// its digest. What goes onto the envelope is the name, so a tool that took the
// list would write a list of somebody's subkeywords in the clear, quoted as
// though it were the name a reader is to pair with the entity.
TEST(ProtectDigestKeynameEncryptionOutput, AListPutsNoNameOnTheEnvelope) {
  std::string envelope = WrittenOutOf(
      Sealing("`pragma protect digest_keyname=(held_by=\"helios-trust\")\n"));
  EXPECT_EQ(envelope.find(kHiddenDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_keyname=\""), std::string::npos) << envelope;
}

// ---------------------------------------------------------------------------
// A reader combines the name with the entity to reach one key.
// ---------------------------------------------------------------------------

// §34.5.18.2: read in a protected envelope, the name is combined with the
// entity to select the single key the digest block is decrypted with. Neither
// reaches it alone, a name being a member of one entity's list and saying
// nothing outside it.
TEST(ProtectDigestKeynameDecryptionInput, TheNameAndTheEntityReachOneKey) {
  ReadingOf run(EnvelopeCarrying(Designates(kProvider, kProviderName)));
  EXPECT_EQ(run.DigestKey(), kProviderKey);
}

// The name standing in the digest's place is paired with the entity exactly as
// a specified one is, so an envelope that named a key for its data and none for
// its digest reaches the key that name and the entity select together.
TEST(ProtectDigestKeynameDecryptionInput, TheNameFilledInIsPairedTheSameWay) {
  std::string described = Written("digest_keyowner", kDataParty);
  described += Written("data_keyname", kDataName);
  ReadingOf run(EnvelopeCarrying(described));
  EXPECT_EQ(run.DigestKey(), kDataKey);
}

// The negative: the same name read under a party that holds no key by it
// reaches nothing, so a digest whose block was sealed under the key the right
// pair names has no key here to open it with.
TEST(ProtectDigestKeynameDecryptionInput,
     ThatNameUnderAnotherPartyReachesNone) {
  ReadingOf run(EnvelopeCarrying(Designates(kOtherProvider, kProviderName)));
  EXPECT_TRUE(run.DigestKey().empty());
}

// ---------------------------------------------------------------------------
// The name travels in a key block where a digital envelope is used.
// ---------------------------------------------------------------------------

// The entity that provided the key a region's own keys travel under, with the
// name picking that key out of its list and the key itself. §34.5.27.2 forms a
// key block for a region designating one, and that block is where §34.5.18.2
// sends the name of the key the digests are under.
constexpr std::string_view kBlockProvider = "cerulean-vault";
constexpr std::string_view kBlockProviderName = "wrapping-2033";
constexpr std::string_view kBlockProviderKey = "cerulean-vault-wrapping-key";

// The expression announcing a key block, which is how a case below tells an
// envelope carrying one from an envelope that carries none.
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

// The region every case below encrypts. It names a key for its digests, names
// an entity and a key for its data, and designates a provider for its own keys,
// so the text says nothing about which of the two arrangements it gets: what
// decides is whether the tool holds the key the data name reaches.
std::string RegionNamingBothProviders() {
  std::string described = Designates(kProvider, kProviderName);
  described += Written("data_keyowner", kDataParty);
  described += Written("data_keyname", kDataName);
  described += Written("key_keyowner", kBlockProvider);
  described += Written("key_keyname", kBlockProviderName);
  return Sealing(described);
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
  keys.Add(KeyOf(kDataParty, kDataName, kDataKey));
  return keys;
}

// §34.5.18.2: the name is output as cleartext in the output file, except where
// a digital envelope is used, in which case it travels inside the key_block
// encrypted under the key_method and the key that key_keyname or key_public_key
// designates. §34.5.27.2 forms a key block on a request for a digital
// signature, so this envelope is the excepted one, and the name stands nowhere
// a reader holding no key can read it.
//
// What the name is inside the block cannot be asserted here. The block is
// encrypted and then encoded, so its characters say nothing about what went
// into it, and the case reading the envelope back is what shows the name
// arrived.
//
// The entity the name is read against is still in the clear, which is what the
// last expectation states. §34.5.16.2 sends that entity to a digest_key_block
// rather than to the key_block this envelope carries, and this tool writes no
// digest_key_block; issue #3429 is that gap. The expectation is here because it
// is what keeps the expectation above it from passing for an envelope that
// dropped every mention of the digest's key.
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

// §34.5.18.2 excepts the digital envelope and nothing else, so an envelope
// carrying no key block states the name in the clear. The source text is the
// text the case above encrypted, character for character; what differs is that
// the tool holds the key the region's data name reaches, so the exception does
// not arise.
TEST(ProtectDigestKeynameEncryptionOutput,
     TheDigestNameStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope =
      EncryptEnvelopes(RegionNamingBothProviders(), {}, TheDataKeyAsWell());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kHiddenDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Written("digest_keyname", kProviderName)))
      << envelope;
}

// The excepted envelope read back by the provider whose key opens its block.
// §34.5.18.2 relocates the name rather than discarding it, so the region still
// opens and the design comes back: an envelope that had dropped the name would
// pass the first case above and fail here.
TEST(ProtectDigestKeynameDecryptionInput,
     TheDigestNameInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheBlockProvidersKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kHiddenDesign)) << run.text;
}

}  // namespace
