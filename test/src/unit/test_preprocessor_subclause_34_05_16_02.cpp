// §34.5.16.2 digest_keyowner, ENCRYPTION OUTPUT.
//
// The paragraph says one thing: "The digest_keyowner shall be unchanged in the
// output file, except where a digital signature is used, in which case it is
// encrypted with the digest_key_method and placed in a digest_key_block."
//
// The standard defines no digest_key_block. §34.4 states that "this standard
// defines the pragma keyword names listed in Table 34-1 for use with the
// `protect` pragma. These pragma keywords are defined in 34.5 with a
// specification of how each participates in the encryption and decryption
// processing modes." Table 34-1 lists 32 keywords; key_block is among them and
// digest_key_block is not. §34.5 runs from §34.5.1 to §34.5.32 without a
// subclause for one, so the construct has neither a Syntax nor a Description.
// §34.5.1.2 enumerates the blocks an envelope carries as "the data_block and
// key_block pragma expressions introduce the encrypted data or keys and will
// always be found within a begin_protected-end_protected envelope", and names
// no third.
//
// The neighbouring subclauses send their values to the key_block instead, which
// is what leaves this one alone in naming a destination nothing defines.
// §34.5.17.2 has the digest_key_method "encrypted with the key_method
// algorithm" and using "the key found in the key_block". §34.5.18.2 has the
// digest_keyname "encrypted using key_method and key_keyname/key_public_key and
// encoded in the key_block". §34.5.16.2 alone names a digest_key_method cipher
// and a digest_key_block destination.
//
// So the exception has no destination, and the main clause is the whole of what
// a conforming tool can act on: the entity a region named for the key its
// digest is under is unchanged in the output file, signature or no signature.
// That is what src/preprocessor/protect_envelope_output.cpp does in
// AppendClearDigestNames, which writes the name whether the envelope carries
// key blocks or not, and it is what the four cases below state. Issue #3429
// settled the reading.
//
// The first case encrypts a region under a signature: it designates an entity
// and a key for its own keys that the tool holds, and an entity and a key for
// its data that the tool does not, so §34.5.27.2 forms a key block. The count
// of key blocks is asserted beside the name, because an unsigned envelope
// states the name too and a case that only read the name back would pass for
// either arrangement. The second case encrypts the same source text, character
// for character, under a key list that reaches the data's own key, so no key
// block is formed and the exception never arises. What the two claim together
// is that §34.5.16.2's exception changes nothing about where the name is
// written.
//
// The third case guards the finding. It searches both envelopes for the
// expression `pragma protect digest_key_block and finds none, so a later change
// that invents the construct rather than reporting the standard's gap fails
// here.
//
// The fourth case reads the signed envelope back under the key that opens its
// block, so the pair above is shown to be about an envelope that works: the
// region opens and the design comes back.
//
// The region asks for a digest with the expression §34.5.22.2 makes a request,
// and names a key of the digest's entity as well as the entity itself, so what
// §34.5.16.2 calls the entity whose key the digest is under is the entity of a
// digest the envelope actually carries. Without the request no digest block is
// written at all and the name on the envelope would stand for nothing.
//
// test_preprocessor_subclause_34_05_16.cpp holds §34.5.16 as a whole, and its
// case ProtectDigestKeyownerEncryptionOutput.AnEnvelopeCarryingKeysStatesItToo
// states that a signed envelope writes the name. What is here and not there is
// the digest the name is the owner of, the unsigned control on the same source
// text, the guard on the construct itself and the reading back.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The design the region seals. Nothing of it survives the writing of an
// encrypted block, so finding it in an envelope is finding a region that was
// never encrypted.
constexpr std::string_view kVouchedDesign = "module vouched_m; endmodule\n";

// The entity that provided the key the region's own keys travel under, the name
// picking that key out of its list, and the key itself. §34.5.27.2 forms a key
// block for a region designating one, and that block is the digital signature
// §34.5.16.2 states its exception for.
constexpr std::string_view kSignatureProvider = "harbor-mark-custody";
constexpr std::string_view kSignatureName = "wrapping-2041";
constexpr std::string_view kSignatureKey = "harbor-mark-wrapping-key";

// The entity the region names for the key its data are under, the name picking
// that key out of its list, and the key itself. Whether the tool holds this one
// is what decides between the two arrangements the cases below compare.
constexpr std::string_view kDesignProvider = "orrery-labs";
constexpr std::string_view kDesignName = "design-2041";
constexpr std::string_view kDesignKey = "orrery-labs-region-key";

// The entity the region names for the key its digest is under, the name picking
// that key out of its list, and the key itself. §34.5.16.2 is about this
// entity's name, and §34.5.16 permits it to be a third party distinct from the
// two above.
constexpr std::string_view kDigestProvider = "solace-notary";
constexpr std::string_view kDigestName = "notary-2041";
constexpr std::string_view kDigestKey = "solace-notary-signing-key";

// The expression announcing a key block, which is how a case tells an envelope
// carrying one from an envelope that carries none.
constexpr std::string_view kKeyBlockExpression = "`pragma protect key_block\n";

// The expression §34.5.22 makes a request for a digest, and announces one in
// what an encrypting tool writes out.
constexpr std::string_view kDigestBlockExpression =
    "`pragma protect digest_block\n";

// The expression §34.5.16.2 names as the destination of the entity's name where
// a digital signature is used. §34.4 admits no such keyword, so no directive
// this tool writes may open with these characters. The value carries no newline
// and no equals sign, so it matches the keyword written standing alone as well
// as the keyword written with a value against it.
constexpr std::string_view kDigestKeyBlockExpression =
    "`pragma protect digest_key_block";

// One protect pragma directive writing `value` against `keyword` as a string.
// It serves both sides: the region is built from these characters, and a tool
// required to leave a name unchanged writes the same ones back, so what a case
// searches for is the spelling the input was built from.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The directive naming the entity whose key the region's digest is under, which
// is the text §34.5.16.2 has standing unchanged in the output file.
std::string NamesTheDigestProvider() {
  return Writes("digest_keyowner", kDigestProvider);
}

// The one region every case below encrypts. It asks for a digest, names an
// entity and a key for that digest, names an entity and a key for its data, and
// designates a provider for its own keys. The text says nothing about which of
// the two arrangements it gets: what decides is whether the tool holds the key
// the data name reaches.
std::string RegionAskingForADigest() {
  std::string text = "`pragma protect begin\n";
  text.append(kDigestBlockExpression);
  text.append(Writes("data_keyowner", kDesignProvider));
  text.append(Writes("data_keyname", kDesignName));
  text.append(NamesTheDigestProvider());
  text.append(Writes("digest_keyname", kDigestName));
  text.append(Writes("key_keyowner", kSignatureProvider));
  text.append(Writes("key_keyname", kSignatureName));
  text.append(kVouchedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The key that opens the region's own key block, beside the key the digest's
// names reach. The region's data name reaches neither, so §34.5.27.2 forms a
// key block and the envelope is the signed one.
ProtectKeyList KeysWithoutTheDesignsOwnKey() {
  ProtectKeyList held;
  held.Add(KeyOf(kSignatureProvider, kSignatureName, kSignatureKey));
  held.Add(KeyOf(kDigestProvider, kDigestName, kDigestKey));
  return held;
}

// Those two keys and the one the region's data name reaches. The region is
// sealed under the third, so no key block is written and no digital signature
// is used.
ProtectKeyList KeysReachingTheDesignsOwnKey() {
  ProtectKeyList held;
  held.Add(KeyOf(kSignatureProvider, kSignatureName, kSignatureKey));
  held.Add(KeyOf(kDigestProvider, kDigestName, kDigestKey));
  held.Add(KeyOf(kDesignProvider, kDesignName, kDesignKey));
  return held;
}

// The envelope this tool writes for that region under `held`, checked on the
// way out to be one that sealed its design and one that carries a digest for
// the named entity to be the owner of the key of.
std::string EnvelopeUnder(const ProtectKeyList& held) {
  std::string envelope = EncryptEnvelopes(RegionAskingForADigest(), {}, held);
  EXPECT_FALSE(Holds(envelope, kVouchedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, kDigestBlockExpression)) << envelope;
  return envelope;
}

// §34.5.16.2: the entity is unchanged in the output file, except where a
// digital signature is used. §34.5.27.2 forms a key block on a request for a
// digital signature, so this envelope is the excepted one, and the name stands
// in it unchanged all the same: the exception sends the name to a
// digest_key_block, and the standard defines none.
//
// The count of key blocks is what makes this the excepted envelope rather than
// an ordinary one, which would state the name whatever §34.5.16.2 said about
// the exception.
TEST(ProtectDigestKeyownerSignedEnvelope,
     TheEntityStandsInTheClearInASignedEnvelope) {
  std::string envelope = EnvelopeUnder(KeysWithoutTheDesignsOwnKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 1U) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDigestProvider())) << envelope;
}

// §34.5.16.2's main clause, with no exception in sight. The source text is the
// text the case above encrypted, character for character; what differs is that
// the tool holds the key the region's data name reaches, so no key block is
// formed. The name stands in the clear here too, which is what says the
// exception changed nothing.
TEST(ProtectDigestKeyownerSignedEnvelope,
     TheEntityStandsInTheClearWithoutASignature) {
  std::string envelope = EnvelopeUnder(KeysReachingTheDesignsOwnKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 0U) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesTheDigestProvider())) << envelope;
}

// §34.4 admits the keyword names Table 34-1 lists and digest_key_block is not
// among them, so neither envelope carries the expression §34.5.16.2 sends the
// name to. A change that answered the subclause by inventing the construct,
// rather than by reporting that the standard defines none, writes that
// expression into the signed envelope and fails here.
TEST(ProtectDigestKeyownerSignedEnvelope,
     NoDigestKeyBlockIsWrittenForTheEntityToTravelIn) {
  std::string signed_envelope = EnvelopeUnder(KeysWithoutTheDesignsOwnKey());
  EXPECT_FALSE(Holds(signed_envelope, kDigestKeyBlockExpression))
      << signed_envelope;
  std::string plain_envelope = EnvelopeUnder(KeysReachingTheDesignsOwnKey());
  EXPECT_FALSE(Holds(plain_envelope, kDigestKeyBlockExpression))
      << plain_envelope;
}

// The signed envelope read back by the provider whose key opens its block. The
// region opens and the design comes back, so the two cases above are about an
// envelope a reader can use rather than about text that happens to hold a name.
TEST(ProtectDigestKeyownerSignedEnvelope,
     TheSignedEnvelopeOpensWithTheEntityInTheClear) {
  PreprocFixture fixture;
  PreprocConfig config;
  config.protect_keys = KeysWithoutTheDesignsOwnKey();
  std::string recovered =
      Preprocess(EnvelopeUnder(KeysWithoutTheDesignsOwnKey()), fixture, config);
  EXPECT_FALSE(fixture.diag.HasErrors()) << recovered;
  EXPECT_TRUE(Holds(recovered, kVouchedDesign)) << recovered;
}

}  // namespace
