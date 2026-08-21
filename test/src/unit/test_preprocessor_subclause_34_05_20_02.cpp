// §34.5.20 digest_decrypt_key.
//
// §34.5.20.2 says four things about the keyword §34.4 tabulates.
//
//   The keyword indicates that the next line contains the encoded value of the
//   key that will decrypt the digest_block. It is what an IP author writes
//   where digital signatures are used: the author generates a key, encrypts
//   the digest under it, and stores that encrypted text as the digest_block.
//
//   The digest_key_method and the digest_decrypt_key are then encrypted under
//   the key_method and stored as the contents of the key_block. The
//   digest_block itself is not reencrypted; only the information about the
//   digest key is.
//
//   Where an input specifies no digest_decrypt_key, the default value of
//   digest_decrypt_key is the current value of data_decrypt_key.
//
//   A tool that has determined a digital signature was in use for a protected
//   region decrypts the key_block to find the digest_decrypt_key and the
//   digest_key_method, and those two decrypt the digest block.
//
// All four are preprocessor-stage rules. The line beneath the keyword is read
// by Preprocessor::TakeDigestDecryptKeyValue and the default is applied by
// Preprocessor::DigestDecryptKeyInEffect, both in
// src/preprocessor/preprocessor_protect_keys.cpp; the pair written into a key
// block is built by ProtectDigestDecryptionContent in
// src/preprocessor/protect_digest_key.cpp and placed by ProtectKeyBlockContent
// in src/preprocessor/protect_key_block.cpp; the key a region's digests are
// sealed under is chosen by RegionEncryptionFor in
// src/preprocessor/protect_processing.cpp; and the comparison a recovered key
// makes possible is CheckProtectDigestBlock in
// src/preprocessor/protect_digest_block.cpp.
//
// Two kinds of input are written below. Where what an encrypting tool does is
// the question, a region delimited by §34.5.1 and §34.5.2 is put through
// EncryptEnvelopes and the envelope that comes back is read. Where what a
// reader does with a block some other tool wrote is the question, the envelope
// is built here from the same block writers, so that the one thing the case
// varies -- which key the digest was sealed under, and whether the block
// carries a key for it -- is the only thing separating two readings.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity that provided the key a region's key blocks are encrypted under,
// and the name picking that key out of the entity's list.
constexpr std::string_view kProvider = "meridian-trust";
constexpr std::string_view kBlockKeyName = "wrapping-2027";
constexpr std::string_view kBlockKey = "meridian-trust-wrapping-key";

// The name a region gives the key its data are under. A name and no key held
// for it is what sends a region to a key block rather than to a key of its
// author's.
constexpr std::string_view kDataKeyName = "design-2027";

// The cipher a region names for the key its digests are under. §34.5.17.2 has
// this identifier travel inside the key block wherever a digital signature is
// in use, which is the block §34.5.20.2 puts the key itself in.
constexpr std::string_view kDigestKeyMethod = "x-meridian-digest-cipher";

// The session key a hand-built key block states for the region's data, and the
// separate one such a block states for the region's digests. Two values rather
// than one, so that a digest sealed under either is a digest the other does not
// open and the case can say which key was reached.
//
// The two differ at their first character rather than at some later one.
// CombineWithKey in src/preprocessor/protect_processing_cipher.cpp walks the
// key alongside the bytes it combines with, taking key[n % key.size()] for
// byte n, so a key reaches only as far into itself as the block is long. A
// digest block here is four fingerprint bytes and a 20-byte SHA-1 digest, and
// two keys agreeing over those 24 characters open it identically however they
// end -- which would leave a case that seals a digest under the wrong key
// unable to fail.
constexpr std::string_view kSessionKey = "opens-the-data-of-this-region";
constexpr std::string_view kDigestSessionKey =
    "unseals-the-digest-of-this-region";

// A key no block of these envelopes ever carries, for the readings that ask
// whether a digest opened because the right key was reached or because any key
// would have done.
constexpr std::string_view kStrangersKey = "a-key-no-block-here-carries";

// The design a region seals.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// A pragma_value written as the string it is. A field a block writer copies out
// unchanged holds the value as the source wrote it, quotation marks and all.
std::string InQuotes(std::string_view value) {
  std::string text = "\"";
  text.append(value).append("\"");
  return text;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The expression §34.5.22 makes a request for a digest in what an encrypting
// tool writes out. It stands ahead of the region rather than inside it, §34.4
// making the scope of the request lexical.
std::string RequestsDigest() { return "`pragma protect digest_block\n"; }

// A region designating the key its key block is under, naming the key its data
// are under, and naming the cipher its digest's key belongs to.
std::string RegionUnderAKeyBlock() {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kProvider));
  text.append(Writes("key_keyname", kBlockKeyName));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(Writes("digest_key_method", kDigestKeyMethod));
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The one key a user holds: the one the region's key blocks are encrypted
// under. The key that opens the digests is not among them, which is what makes
// a digest that opens say the block carried its key.
ProtectKeyList TheBlockKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kProvider, kBlockKeyName, kBlockKey));
  return keys;
}

// The envelope this tool writes for that region, checked on the way out to be
// one carrying both a key block and a digest block: without either, the cases
// below would be about a region sealed some other way.
std::string EnvelopeWithASignedKeyBlock() {
  std::string envelope = EncryptEnvelopes(
      RequestsDigest() + RegionUnderAKeyBlock(), {}, TheBlockKey());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  EXPECT_NE(envelope.find("`pragma protect digest_block"), std::string::npos)
      << envelope;
  return envelope;
}

// The contents §34.5.20.2 has a key block hold: the key that opens the data,
// and beside it the cipher and the key that open the digest. `digest_key` empty
// is the block of an input that specified no digest_decrypt_key.
std::string BlockContentCarrying(std::string_view digest_key) {
  ProtectDataDecryption data;
  data.method = std::string(kDataMethod);
  data.decrypt_key = std::string(kSessionKey);
  ProtectDigestDecryption digest;
  // ProtectDigestDecryptionContent writes this field into the block exactly as
  // it stands, which is what protect_digest_key.h asks of whoever fills it: the
  // value is the pragma_value the source wrote, quotation marks included. An
  // identifier holding a hyphen and put here bare goes into the block as a
  // directive §22.11 rejects for the token the hyphen is.
  digest.key_method = InQuotes(kDigestKeyMethod);
  digest.decrypt_key = std::string(digest_key);
  return ProtectKeyBlockContent(data, digest, DefaultProtectEncoding());
}

// A decryption envelope whose key block carries `digest_key` and whose digest
// block is sealed under `sealed_under`.
//
// The digest stands beside the key block rather than inside it, which is where
// §34.5.20.2 leaves it: the block carrying the key is what the digest is
// computed over, and a reader recomputes it from what that block opened to.
std::string EnvelopeSealingItsDigestUnder(std::string_view digest_key,
                                          std::string_view sealed_under) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  std::string content = BlockContentCarrying(digest_key);
  ProtectKeyBlockRequest request;
  request.keyowner = std::string(kProvider);
  // §34.5.23 has the entity written into the block's own directive in the
  // spelling the source used, so a request carries the value as written beside
  // the body of it that reaches a key. This one is built here rather than read
  // from a source, and the two spellings of a name holding no quotation marks
  // are the same characters.
  request.stated_keyowner = std::string(kProvider);
  request.keyname = std::string(kBlockKeyName);
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(sealed_under);
  std::string text = "`pragma protect begin_protected\n";
  text.append(ProtectKeyBlockDirectives(request, content, kBlockKey, encoding));
  text.append(ProtectDigestBlockDirectives(content, policy, encoding));
  text.append("`pragma protect end_protected\n");
  return text;
}

// A reading of `src` by a tool holding `keys`, with the preprocessor kept alive
// afterwards.
//
// What §34.5.20 leaves behind is not output text but how a digest came out:
// whether the key the reading reached is the key the digest was sealed under.
// That belongs to the point the reading has got to rather than to any one
// directive, so it is read off the preprocessor once the whole text has passed
// through.
struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys)
      : pp(mgr, diag, KeysConfig(keys)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig KeysConfig(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }

  // How the digest block the reading last reached compared against the block it
  // follows. A digest sealed under some other key than the one this reading
  // reached does not open at all, so this tells a digest opened under the key
  // §34.5.20 leads to from a digest opened under any other.
  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// ---------------------------------------------------------------------------
// The line beneath the keyword is the key that opens the digest block.
// ---------------------------------------------------------------------------

// §34.5.20.2: the keyword indicates that the next line contains the encoded
// value of the key that will decrypt the digest_block. The block below carries
// a key of the digest's own, distinct from the one it carries for the data, and
// the digest was sealed under that one; the digest opens and agrees with the
// block it follows, so the line beneath the keyword is what the reading opened
// it with.
TEST(ProtectDigestDecryptKeyDescription, TheKeyTheBlockCarriesOpensTheDigest) {
  ReadUnderKeys run(
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kDigestSessionKey),
      TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The same block carrying the same key, with the digest sealed under the key
// the block states for the data instead. The reading reaches the key the
// keyword announced rather than the one the data are under, so the digest does
// not open -- which is what makes the case above about the announced key rather
// than about there being a key anywhere in the block.
TEST(ProtectDigestDecryptKeyDescription,
     ADigestSealedUnderTheDataKeyDoesNotOpen) {
  ReadUnderKeys run(
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kSessionKey),
      TheBlockKey());
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The same block again, with the digest sealed under a key no block of the
// envelope carries. Nothing the reading can reach opens it, which is the
// outcome a reading that reached the wrong key shares with one that reached
// none: the case above says the announced key is what was reached, and this one
// says an unreachable key is not.
TEST(ProtectDigestDecryptKeyDescription,
     ADigestSealedUnderAStrangersKeyDoesNotOpen) {
  ReadUnderKeys run(
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kStrangersKey),
      TheBlockKey());
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// §34.5.20.2: the digest_block itself is not reencrypted; only the information
// about the digest key is. The envelope this tool writes states its digest
// block beside the key block rather than inside it, so a reader that has opened
// the key block finds the digest already in hand.
TEST(ProtectDigestDecryptKeyDescription, TheDigestBlockStandsOutsideTheKeyOne) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  EXPECT_NE(envelope.find("`pragma protect digest_block"), std::string::npos)
      << envelope;
}

// ---------------------------------------------------------------------------
// An input specifying no key for its digest leaves it under the data's.
// ---------------------------------------------------------------------------

// §34.5.20.2: where no digest_decrypt_key is specified in the input, the
// default is the current value of data_decrypt_key. The block below carries a
// key for the data and none for the digest, and the digest was sealed under
// that data key; the digest opens, so the empty place was filled from the key
// the block states for the data.
TEST(ProtectDigestDecryptKeyDefault, ABlockCarryingNoneUsesTheDataKey) {
  ReadUnderKeys run(EnvelopeSealingItsDigestUnder({}, kSessionKey),
                    TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The same block carrying no key for its digest, with the digest sealed under a
// key nothing in the envelope states. The default reaches the data's key rather
// than whatever key is nearest, so this digest does not open.
TEST(ProtectDigestDecryptKeyDefault, ThatDefaultIsTheDataKeyAndNoOther) {
  ReadUnderKeys run(EnvelopeSealingItsDigestUnder({}, kStrangersKey),
                    TheBlockKey());
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The default is the current value of data_decrypt_key, and what is current is
// decided where the digest is read. Two envelopes stand here: the first carries
// a key of its own for its digest, and the second carries none and has its
// digest sealed under its own data key. The second opens, so the key the first
// envelope's block carried was not left standing over it.
TEST(ProtectDigestDecryptKeyDefault, TheKeyOfAnEarlierEnvelopeIsNotCurrent) {
  std::string src =
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kDigestSessionKey);
  src += EnvelopeSealingItsDigestUnder({}, kSessionKey);
  ReadUnderKeys run(src, TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// ---------------------------------------------------------------------------
// What an encrypting tool writes the key into.
// ---------------------------------------------------------------------------

// §34.5.20.2: the digest_decrypt_key is output as part of the encrypted content
// of the key_block. An envelope this tool writes for a region asking for a
// digest states the keyword nowhere in the clear, the one place it is written
// being inside the block a reader has to open first.
TEST(ProtectDigestDecryptKeyEncryptionOutput, TheKeywordIsNowhereInTheClear) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  EXPECT_EQ(envelope.find("digest_decrypt_key"), std::string::npos) << envelope;
}

// The cipher §34.5.17 names for that key is stored beside it and not in the
// clear either, which is the exception §34.5.17.2 states for an envelope
// carrying key blocks. A region naming one has that identifier nowhere on the
// envelope.
TEST(ProtectDigestDecryptKeyEncryptionOutput, TheCipherIsNotInTheClearEither) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  EXPECT_EQ(envelope.find(kDigestKeyMethod), std::string::npos) << envelope;
}

// ---------------------------------------------------------------------------
// What a reader takes out of the key block.
// ---------------------------------------------------------------------------

// §34.5.20.2: a tool that has determined a digital signature was in use
// decrypts the key_block to find the digest_decrypt_key and the
// digest_key_method, and those decrypt the digest block. The whole round trip,
// through both halves of the tool: a region is sealed into an envelope carrying
// key blocks, and a reader holding the one key that opens those blocks gets the
// design back and finds the digest agreeing with the block it follows.
TEST(ProtectDigestDecryptKeyDecryptionInput,
     TheKeyBlockYieldsWhatOpensTheData) {
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), TheBlockKey());
  EXPECT_TRUE(run.Holds("module sealed_m")) << run.text;
}

// The same round trip, on the digest. The key that sealed it is neither the key
// the reader supplied nor the key the block states for the data, so a digest
// that opens says the reading took the digest's own key out of the block.
TEST(ProtectDigestDecryptKeyDecryptionInput, TheDigestOpensUnderTheCarriedKey) {
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The other half of what the block is decrypted to find. The cipher the region
// named for its digest's key is written nowhere on the envelope, so a reading
// that has it in effect afterwards took it out of the block, which is where
// §34.5.20.2 sends a reader for it.
TEST(ProtectDigestDecryptKeyDecryptionInput, TheKeyBlockYieldsTheCipherToo) {
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), TheBlockKey());
  EXPECT_EQ(run.ValueOf("digest_key_method").value, kDigestKeyMethod);
}

// The negative: a reader holding the wrong key for the entity the blocks were
// written for. The key block does not open, so nothing is recovered for the
// digest's key to be taken out of, and no digest is checked at all: §34.5.22
// has a digest stand for the block it follows, and a reader that recovered no
// block has nothing for a digest to be the digest of. That is what tells this
// reading from the one above, where the same envelope under the right key
// checks a digest and finds it agrees.
TEST(ProtectDigestDecryptKeyDecryptionInput, AReaderWithoutTheKeyReachesNone) {
  ProtectKeyList strangers;
  strangers.Add(KeyOf(kProvider, kBlockKeyName, kStrangersKey));
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), strangers);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

}  // namespace
