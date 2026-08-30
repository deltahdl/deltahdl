// §34.5.26 key_public_key, Description.
//
// §34.5.26.2 says four things about the keyword §34.5.26.1 spells.
//
//   The line beneath the keyword carries the encoded value of the public key
//   the region's key data are to be encrypted under, written in the coding
//   scheme the encoding pragma expression in effect names.
//
//   Where a text writes both this designation and the name §34.5.25 spells,
//   the two shall refer to the same key.
//
//   The expression is output in each protected block it was used for, with the
//   encoded value beneath it.
//
//   On the way back, the entity and the identifier naming the cipher the keys
//   are under can be combined with this designation to decide whether the tool
//   knows the private key that opens a given key block.
//
// The first three are what this file states. Which spelling of the expression
// speaks for the line beneath it is §34.5.26.1's and is stated in
// test_preprocessor_subclause_34_05_26_01.cpp; what is left here is the scheme
// that line is read under, the agreement the two designations are held to, and
// the blocks the designation is written into.
//
// The fourth names three things combined and this implementation combines two.
// ProtectKeyBlockKey in src/preprocessor/protect_keywords.cpp reads the entity
// and the designation and no identifier at all, and #3278 records that nothing
// in a run reads the one §34.5.24 spells, along with what stands in the way of
// reading it. A case below states the consequence rather than the rule: a block
// opens whatever cipher the envelope named for it.
//
// Knowing the private key is a lookup here rather than a computation. A key is
// held under an entity and a designation, and §34.5.26 makes the public key one
// of the designations a key may be held under, so a tool knows the private key
// exactly when it was handed a key under those characters.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity whose keys a region's own keys travel under, and the two
// designations a text may reach one of its keys by. They are different
// characters: §34.5.23 reports one value written against both of the names
// designating a key, so a case writing one value twice would reach that rule
// rather than the one this file is about.
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kPublicKey = "acme-public-key-of-2027";

// The key each designation reaches, and a second key for the case where they
// reach two.
constexpr std::string_view kTheKey = "meridian-trust-wrapping-key";
constexpr std::string_view kAnotherKey = "meridian-trust-key-of-2026";

// The name a region gives the key its data are under. A name with no key held
// for it is what sends the region to a key block rather than to a key of its
// author's, which is where the designation is written.
constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The report §34.5.26 draws from two designations reaching two keys.
constexpr std::string_view kDisagreement =
    "key_public_key and key_keyname designate different keys of the "
    "key_keyowner in effect";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// `key` written under the coding scheme a text that stated none is read in.
std::string Encoded(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

// The designation §34.5.26.1 spells: the keyword standing alone with the
// encoded value on the line beneath it.
std::string DesignatesByPublicKey(std::string_view key) {
  std::string text = "`pragma protect key_public_key\n";
  text.append(Encoded(key)).append("\n");
  return text;
}

// A decryption envelope as some other tool wrote it, carrying `described`.
std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

// A tool holding one key under each designation. Where the two values are the
// same key the designations agree; where they differ the text has designated
// two of the entity's keys and said they are one.
PreprocConfig HoldingBothDesignations(std::string_view under_name,
                                      std::string_view under_public) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, under_name));
  keys.Add(KeyOf(kEntity, kPublicKey, under_public));
  PreprocConfig config;
  config.protect_keys = keys;
  return config;
}

// A tool holding a key under the name alone, for the reading that cannot tell
// whether the two designations agree.
PreprocConfig HoldingTheNameAlone() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  PreprocConfig config;
  config.protect_keys = keys;
  return config;
}

// An encryption region designating its key by the public key, and naming for
// its data a key nobody holds so that its own keys travel in a block.
std::string RegionDesignating(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kEntity));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The one key an encrypting run holds, held under the public key designation.
ProtectKeyList HeldUnderThePublicKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kPublicKey, kTheKey));
  return keys;
}

// -- The two designations refer to one key -----------------------------------

// §34.5.26.2: where a text writes both designations they shall refer to the
// same key. This tool holds a key under each and they are two different keys,
// so the text has designated two and said they are one.
//
// The report stands where the pair was completed, which is the line the second
// designation was read from -- here the encoded value beneath the keyword.
TEST(ProtectKeyPublicKeyDescription,
     TwoDesignationsReachingTwoKeysAreReported) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     Writes("key_keyname", kKeyName) +
                                     DesignatesByPublicKey(kPublicKey));
  PreprocFixture f;
  Preprocess(src, f, HoldingBothDesignations(kTheKey, kAnotherKey));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDisagreement,
                            LineHolding(src, Encoded(kPublicKey)), "34.5.26"));
}

// The same text read by a tool for which the two designations reach one key.
// Nothing is reported, without which the case above would hold of a reading
// that reported every text writing both.
TEST(ProtectKeyPublicKeyDescription,
     TwoDesignationsReachingOneKeyAreNotReported) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     Writes("key_keyname", kKeyName) +
                                     DesignatesByPublicKey(kPublicKey));
  PreprocFixture f;
  Preprocess(src, f, HoldingBothDesignations(kTheKey, kTheKey));
  EXPECT_FALSE(f.diag.HasErrors());
}

// A tool holding a key under one designation and nothing under the other
// cannot tell a text that designated one key from a text that designated two.
// There is no second key for the first to disagree with, so what the text wrote
// stands and nothing is said about it.
TEST(ProtectKeyPublicKeyDescription,
     ADesignationReachingNoHeldKeyLeavesTheOtherAlone) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     Writes("key_keyname", kKeyName) +
                                     DesignatesByPublicKey(kPublicKey));
  PreprocFixture f;
  Preprocess(src, f, HoldingTheNameAlone());
  EXPECT_FALSE(f.diag.HasErrors());
}

// The pair is completed by whichever designation is written second, so a text
// writing them the other way round is reported at the other line. Without this
// the rule would read as one about the public key following the name.
TEST(ProtectKeyPublicKeyDescription, TheNameWrittenLastCompletesThePair) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     DesignatesByPublicKey(kPublicKey) +
                                     Writes("key_keyname", kKeyName));
  PreprocFixture f;
  Preprocess(src, f, HoldingBothDesignations(kAnotherKey, kTheKey));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDisagreement,
                            LineHolding(src, "`pragma protect key_keyname"),
                            "34.5.26"));
}

// -- The scheme the value is read under --------------------------------------

// §34.5.26.2: the value is encoded as the encoding pragma expression in effect
// specifies. A line that is not written in that scheme is no encoded value, and
// §34.5.9.2 reports it where the reading meets it.
TEST(ProtectKeyPublicKeyDescription, AValueOutsideTheSchemeInEffectIsReported) {
  std::string src = EnvelopeCarrying(
      "`pragma protect encoding=(enctype=\"base64\")\n"
      "`pragma protect key_public_key\n"
      "not base64 at all!!\n");
  PreprocFixture f;
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(), "value is not written in the encoding in effect",
      LineHolding(src, "not base64 at all!!"), "34.5.9.2"));
}

// A line the scheme in effect never wrote designates no key, so the keyword
// above it is left designating nothing rather than designating the characters.
TEST(ProtectKeyPublicKeyDescription, AValueOutsideTheSchemeDesignatesNothing) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile(
      "<test>",
      EnvelopeCarrying("`pragma protect encoding=(enctype=\"base64\")\n"
                       "`pragma protect key_public_key\n"
                       "not base64 at all!!\n")));
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf(kKeyPublicKeyKeyword).value.empty());
}

// -- The blocks the designation is written into ------------------------------

// §34.5.26.2: the expression is output in each protected block it was used for,
// with the encoded value beneath it. A region reaching its key by this
// designation is written a block headed by it.
TEST(ProtectKeyPublicKeyDescription, TheDesignationHeadsTheBlockItWasUsedFor) {
  std::string envelope =
      EncryptEnvelopes(RegionDesignating(DesignatesByPublicKey(kPublicKey)), {},
                       HeldUnderThePublicKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_public_key")) << envelope;
}

// §34.5.26 makes the name and the public key alternatives, so a block carries
// whichever designation the region reached its key by and not both. A region
// reaching its key by name is written a block headed by the name, with no
// designation of this kind in it at all.
TEST(ProtectKeyPublicKeyDescription, ABlockReachedByNameCarriesNoPublicKey) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  std::string envelope = EncryptEnvelopes(
      RegionDesignating(Writes("key_keyname", kKeyName)), {}, keys);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_FALSE(Holds(envelope, "key_public_key")) << envelope;
}

// A designation reaching no key of the entity is written into no block, there
// being no block: the region asked for one, the request reached nothing, and
// what comes back is the region as it stood.
TEST(ProtectKeyPublicKeyDescription, ADesignationReachingNoKeyHeadsNoBlock) {
  std::string region = RegionDesignating(DesignatesByPublicKey(kPublicKey));
  EXPECT_EQ(EncryptEnvelopes(region, {}, ProtectKeyList()), region);
}

// -- What the cipher the envelope names decides ------------------------------

// §34.5.26.2 combines the entity and the identifier naming the cipher with this
// designation to decide whether the private key is known, and this reading
// combines the entity and the designation alone: the identifier decides nothing
// about whether a block opens.
//
// The envelope names the cipher its blocks are really under, which is not
// necessarily the one the region asked for. #3278 settled that a region asking
// for a cipher this tool does not provide is refused rather than written out
// with an identifier its blocks contradict, so the case names the cipher the
// tool provides and the claim it makes is about the designation.
TEST(ProtectKeyPublicKeyDescription, TheCipherNamedDecidesNothingAboutOpening) {
  std::string envelope =
      EncryptEnvelopes(RegionDesignating(Writes("key_method", kDataMethod) +
                                         DesignatesByPublicKey(kPublicKey)),
                       {}, HeldUnderThePublicKey());
  EXPECT_TRUE(Holds(envelope, Writes("key_method", kDataMethod))) << envelope;
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = HeldUnderThePublicKey();
  Preprocessor pp(mgr, diag, std::move(config));
  EXPECT_TRUE(
      Holds(pp.Preprocess(mgr.AddFile("<test>", envelope)), kSealedDesign));
}

}  // namespace
