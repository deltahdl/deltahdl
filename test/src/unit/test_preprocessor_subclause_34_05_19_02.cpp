// §34.5.19.2 digest_public_key, Description.
//
// The subclause says five things about the keyword §34.5.19.1 spells.
//
//   Written in an encrypting tool's input, it states that the next line of the
//   file holds the encoded value of the public key the region's digest is
//   encrypted under.
//
//   How that line is read is settled by the encoding pragma expression
//   currently in effect.
//
//   Where a region wrote this designation and a digest_keyname as well, the two
//   shall refer to the same key.
//
//   Where an input designates no public key for its digest, the designation in
//   effect is the one the region's data carry.
//
//   The expression is written into each protected block it was used for,
//   followed by the encoded value, and a tool reading an envelope combines it
//   with the digest_keyowner to decide whether it holds the private key that
//   opens the digest_block.
//
// All five are preprocessor-stage rules. The line beneath the keyword is read
// by Preprocessor::TakeDigestPublicKeyValue and the pair is held to referring
// to one key by Preprocessor::CheckDigestDesignationAgreement, both in
// src/preprocessor/preprocessor_protect_keys.cpp. The designation standing
// where a region wrote none is ProtectKeywordScope::DigestPublicKeyInEffect in
// src/preprocessor/protect_keywords.cpp, and the key it reaches with the entity
// beside it is ProtectDigestKeyByPublicKey in
// src/preprocessor/protect_digest_block.cpp. What an encrypting tool writes
// into the block is AppendDigestPublicKey in
// src/preprocessor/protect_envelope_output.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// Regions are delimited by §34.5.1 and §34.5.2 where a tool's output is what is
// being observed, and by §34.5.3 and §34.5.4 where the input is an envelope
// some other tool wrote.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity that provided the key a region's digest is under, and a second
// entity holding keys of its own. With one entity in the tool's hands a reading
// that never looked at the entity would answer the same as one that did.
constexpr std::string_view kProvider = "veritas-signing";
constexpr std::string_view kOtherProvider = "globex-ip";

// The two designations §34.5.19 has referring to one key: the public key one of
// the provider's keys is, and the name given to another of them.
constexpr std::string_view kPublicKey = "veritas-rsa-public-key";
constexpr std::string_view kKeyName = "veritas-digest-2027";

// The keys those designations reach. Where a case is about the two agreeing
// they reach the first; where it is about them disagreeing the name reaches the
// second.
constexpr std::string_view kDigestKey = "veritas-digest-signing-key";
constexpr std::string_view kOtherDigestKey = "veritas-some-other-key-entirely";

// The public key a region's data carry, which is what fills the digest's place
// where the digest designated none. It is a different key of the same provider,
// so a digest read under one of them was not read under the other.
constexpr std::string_view kDataPublicKey = "veritas-rsa-data-public-key";

// The key an author supplies directly, so that a region is encrypted whatever
// its own designations reach. What a case about the output watches is the
// designation written beside the block rather than which key sealed it.
constexpr std::string_view kExchangeKey = "veritas-region-exchange-key";

// The design a region seals. Nothing of it survives the writing of an encrypted
// block, so finding it in what a tool wrote is finding a region that was never
// encrypted.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The report a pair of designations reaching two keys draws.
constexpr std::string_view kDisagreement =
    "digest_public_key and digest_keyname designate different keys of the "
    "digest_keyowner in effect";

// The coding scheme a text that stated none is read and written under.
ProtectEncoding PlainEncoding() { return DefaultProtectEncoding(); }

// One of the two Table 34-2 requires of every implementation, for the inputs
// that state a scheme of their own.
ProtectEncoding Base64Encoding() {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBase64Enctype);
  return encoding;
}

// The directive §34.5.9 states a coding scheme with.
std::string StatesEncoding(std::string_view enctype) {
  std::string text = "`pragma protect encoding=(enctype=\"";
  text.append(enctype).append("\")\n");
  return text;
}

// The directive §34.5.16 names the digest's provider with.
std::string NamesProvider(std::string_view provider) {
  std::string text = "`pragma protect digest_keyowner=\"";
  text.append(provider).append("\"\n");
  return text;
}

// The directive §34.5.18 names one of that provider's keys with.
std::string NamesDigestKey(std::string_view keyname) {
  std::string text = "`pragma protect digest_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

// The two lines §34.5.19 spells a designation over: the keyword standing alone,
// and `key` written under `encoding` on the line beneath it.
//
// It serves both sides. A source text designating a key writes these two lines,
// and an encrypting tool writing the designation into the block it was used for
// writes the same two, so what a tool produced is compared against the spelling
// an input is built from.
std::string DigestPublicKeyDesignation(std::string_view key,
                                       const ProtectEncoding& encoding) {
  std::string text = "`pragma protect digest_public_key\n";
  text.append(EncodeProtectBlock(key, encoding)).append("\n");
  return text;
}

// §34.5.13 spells the designation a region's data carry over the same two
// lines, which is what fills the digest's place where the digest wrote none.
std::string DataPublicKeyDesignation(std::string_view key) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(key, PlainEncoding())).append("\n");
  return text;
}

// One encryption envelope: the delimiters of §34.5.1 and §34.5.2 with
// `described` and then the design between them.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

// A decryption envelope as some other tool wrote it: the delimiters of §34.5.3
// and §34.5.4 with `described` between them. It is written out here rather than
// produced, because the expressions an envelope of this tool's own making
// carries always stand in one order, and a tool reads envelopes it did not
// produce.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

// A user holding one key of `owner`, picked out by `designation`.
ProtectKeyList OneKeyUnder(std::string_view owner, std::string_view designation,
                           std::string_view key) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(designation), std::string(key)});
  return keys;
}

// A user holding two keys of the provider, one under each of the two
// designations §34.5.19 has referring to one key.
ProtectKeyList KeysUnderBothDesignations(std::string_view under_public,
                                         std::string_view under_name) {
  ProtectKeyList keys;
  keys.Add({std::string(kProvider), std::string(kPublicKey),
            std::string(under_public)});
  keys.Add(
      {std::string(kProvider), std::string(kKeyName), std::string(under_name)});
  return keys;
}

// A reading of `src` by a tool holding `keys`, with the preprocessor kept alive
// afterwards. What §34.5.19.2 leaves behind is a designation and the key it
// reaches with the entity beside it, and both belong to the point the reading
// has got to rather than to any one directive.
struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys)
      : pp(mgr, diag, Configured(keys)) {
    pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig Configured(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }

  ProtectKeywordValue Designated() const {
    return pp.ProtectKeywords().DigestPublicKeyInEffect();
  }

  // The key a digest block is opened with, which is where the designation
  // written as a public key is reached from.
  std::string_view DigestBlockKey() const {
    return pp.DigestBlockKeyInEffect();
  }
};

// What a tool wrote where the encryption envelopes of `src` stood, for an
// author who supplied one key of their own.
std::string WrittenOutOf(const std::string& src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

// ---------------------------------------------------------------------------
// The line beneath the keyword holds the encoded value of the public key.
// ---------------------------------------------------------------------------

// §34.5.19.2: the next line of the file holds the encoded value of the public
// key the digest is encrypted under. What stands in effect afterwards is that
// value, read out of the coding scheme the text is under.
TEST(ProtectDigestPublicKeyDescription, TheLineBeneathTheKeywordIsTheValue) {
  ReadUnderKeys run(
      ForeignEnvelope(DigestPublicKeyDesignation(kPublicKey, PlainEncoding())),
      ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kPublicKey);
}

// §34.5.19.2: how the line is read is settled by the encoding pragma
// expression currently in effect. The same key written under a scheme the text
// states for itself comes back the same key, the characters on the line being
// different ones.
TEST(ProtectDigestPublicKeyDescription, TheEncodingInEffectReadsTheLine) {
  std::string described = StatesEncoding(kBase64Enctype);
  described += DigestPublicKeyDesignation(kPublicKey, Base64Encoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kPublicKey);
}

// The negative that makes the case above about the scheme: characters written
// under one scheme and read under another are not the key that was encoded. The
// text states no scheme, so the line is read under this implementation's own
// while it was written under base64.
TEST(ProtectDigestPublicKeyDescription, ALineReadUnderAnotherSchemeIsNotIt) {
  ReadUnderKeys run(
      ForeignEnvelope(DigestPublicKeyDesignation(kPublicKey, Base64Encoding())),
      ProtectKeyList());
  EXPECT_NE(run.Designated().value, kPublicKey);
}

// §34.5.19.2: the designation and the entity reach one key together, which is
// the key a region's digest block is opened with. Neither reaches it alone.
TEST(ProtectDigestPublicKeyDescription, TheDesignationAndTheEntityReachOneKey) {
  std::string described = NamesProvider(kProvider);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    OneKeyUnder(kProvider, kPublicKey, kDigestKey));
  EXPECT_EQ(run.DigestBlockKey(), kDigestKey);
}

// The negative: the same designation read under a party that holds no key by it
// reaches nothing, so the entity beside it is what decided the case above.
TEST(ProtectDigestPublicKeyDescription,
     ThatDesignationUnderAnotherPartyReachesNone) {
  std::string described = NamesProvider(kOtherProvider);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    OneKeyUnder(kProvider, kPublicKey, kDigestKey));
  EXPECT_TRUE(run.DigestBlockKey().empty());
}

// ---------------------------------------------------------------------------
// A region writing both designations wrote two names for one key.
// ---------------------------------------------------------------------------

// §34.5.19.2: where both are present they shall refer to the same key. This
// provider holds a key under each designation and they are two different keys,
// so the region has left its digest with no single key to be read under.
TEST(ProtectDigestPublicKeyAgreement, TwoDesignationsReachingTwoKeysReported) {
  std::string described = NamesProvider(kProvider);
  described += NamesDigestKey(kKeyName);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  std::string envelope = ForeignEnvelope(described);
  ReadUnderKeys run(envelope,
                    KeysUnderBothDesignations(kDigestKey, kOtherDigestKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), kDisagreement,
      LineHolding(envelope, EncodeProtectBlock(kPublicKey, PlainEncoding())),
      "34.5.19"));
}

// The same region whose two designations reach one key raises nothing, which is
// what keeps the report above from being something writing both produces on its
// own.
TEST(ProtectDigestPublicKeyAgreement, TwoDesignationsReachingOneKeyAccepted) {
  std::string described = NamesProvider(kProvider);
  described += NamesDigestKey(kKeyName);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeysUnderBothDesignations(kDigestKey, kDigestKey));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The pair is held to referring to one key whichever of the two was written
// first. Here the name arrives after the line carrying the public key, so it is
// the name that completes the pair and the disagreement is reached from there.
TEST(ProtectDigestPublicKeyAgreement, TheNameWrittenLastCompletesThePair) {
  std::string described = NamesProvider(kProvider);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  described += NamesDigestKey(kKeyName);
  std::string envelope = ForeignEnvelope(described);
  ReadUnderKeys run(envelope,
                    KeysUnderBothDesignations(kDigestKey, kOtherDigestKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), kDisagreement,
      LineHolding(envelope, "`pragma protect digest_keyname"), "34.5.19"));
}

// A tool holding a key under only one of the two designations has no second key
// for the first to disagree with, so what the region wrote stands. The source
// is the one that was reported, read against a shorter list of keys, so the
// list is what decided it.
TEST(ProtectDigestPublicKeyAgreement,
     OneDesignationReachingNothingDecidesNone) {
  std::string described = NamesProvider(kProvider);
  described += NamesDigestKey(kKeyName);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described),
                    OneKeyUnder(kProvider, kKeyName, kOtherDigestKey));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// ---------------------------------------------------------------------------
// Where the digest designated no public key, the data's stands in its place.
// ---------------------------------------------------------------------------

// §34.5.19.2: the default value is the current value of data_public_key. This
// text designates a public key for its data and none for its digest.
TEST(ProtectDigestPublicKeyDefault, TheDataDesignationFillsThePlaceLeftEmpty) {
  ReadUnderKeys run(ForeignEnvelope(DataPublicKeyDesignation(kDataPublicKey)),
                    ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kDataPublicKey);
}

// The same reading, on where that value came from. A default rule put it there
// rather than a line beneath the digest's own keyword, and a case reading only
// the characters cannot tell the two apart.
TEST(ProtectDigestPublicKeyDefault, ThePlaceFilledFromTheDataIsADefault) {
  ReadUnderKeys run(ForeignEnvelope(DataPublicKeyDesignation(kDataPublicKey)),
                    ProtectKeyList());
  EXPECT_TRUE(run.Designated().defaulted);
}

// The negative: a region that designated a public key for its digest is under
// that designation, and it is not a default. Without this the two cases above
// would hold of a reading that answered with the data's designation whatever
// the digest wrote.
TEST(ProtectDigestPublicKeyDefault, ADesignationForTheDigestIsNoDefault) {
  std::string described = DataPublicKeyDesignation(kDataPublicKey);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_FALSE(run.Designated().defaulted);
}

// The value that designation leaves in effect, read beside the case above: the
// digest's own rather than the data's, though both were written.
TEST(ProtectDigestPublicKeyDefault, ADesignationForTheDigestIsWhatStands) {
  std::string described = DataPublicKeyDesignation(kDataPublicKey);
  described += DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  ReadUnderKeys run(ForeignEnvelope(described), ProtectKeyList());
  EXPECT_EQ(run.Designated().value, kPublicKey);
}

// A text that designated no public key anywhere has nothing for the default to
// fill the place from, so none stands for its digest at all. That is what makes
// the cases above about the data's designation rather than about any value at
// all.
TEST(ProtectDigestPublicKeyDefault, WithNeitherDesignationWrittenNoneStands) {
  ReadUnderKeys run(ForeignEnvelope(NamesProvider(kProvider)),
                    ProtectKeyList());
  EXPECT_TRUE(run.Designated().value.empty());
}

// ---------------------------------------------------------------------------
// The expression is written into each protected block it was used for.
// ---------------------------------------------------------------------------

// §34.5.19.2: the expression is output in each protected block it is used for,
// followed by the encoded value. The design it was written beside is gone, so
// the text holding the designation is an envelope rather than a region that was
// never encrypted.
TEST(ProtectDigestPublicKeyEncryptionOutput, TheDesignationIsWrittenOut) {
  std::string designation =
      DigestPublicKeyDesignation(kPublicKey, PlainEncoding());
  std::string envelope = WrittenOutOf(Region(designation));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find(designation), std::string::npos) << envelope;
}

// The negative: a region that designated no public key for its digest has none
// written for it. A tool writing one there would designate a key the input
// never named, and a reader would then look for a private key answering to it.
TEST(ProtectDigestPublicKeyEncryptionOutput, ARegionDesignatingNoneGetsNone) {
  std::string envelope = WrittenOutOf(Region(NamesProvider(kProvider)));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("digest_public_key"), std::string::npos) << envelope;
}

}  // namespace
