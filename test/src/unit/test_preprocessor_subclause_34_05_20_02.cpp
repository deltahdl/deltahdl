#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_encoding.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
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

constexpr std::string_view kProvider = "meridian-trust";
constexpr std::string_view kBlockKeyName = "wrapping-2027";
constexpr std::string_view kBlockKey = "meridian-trust-wrapping-key";

constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kDigestKeyMethod = "x-meridian-digest-cipher";

constexpr std::string_view kSessionKey = "opens-the-data-of-this-region";
constexpr std::string_view kDigestSessionKey =
    "unseals-the-digest-of-this-region";

constexpr std::string_view kStrangersKey = "a-key-no-block-here-carries";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string RequestsDigest() { return "`pragma protect digest_block\n"; }

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

ProtectKeyList TheBlockKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kProvider, kBlockKeyName, kBlockKey));
  return keys;
}

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

std::string BlockContentCarrying(std::string_view digest_key) {
  ProtectDataDecryption data;
  data.method = std::string(kDataMethod);
  data.decrypt_key = std::string(kSessionKey);
  ProtectDigestDecryption digest;
  digest.key_method = InQuotes(kDigestKeyMethod);
  digest.decrypt_key = std::string(digest_key);
  return ProtectKeyBlockContent(data, digest, DefaultProtectEncoding());
}

std::string EnvelopeSealingItsDigestUnder(std::string_view digest_key,
                                          std::string_view sealed_under) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  std::string content = BlockContentCarrying(digest_key);
  ProtectKeyBlockRequest request;
  request.keyowner = std::string(kProvider);
  request.stated_keyowner = InQuotes(kProvider);
  request.keyname = std::string(kBlockKeyName);
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(sealed_under);
  std::string text = "`pragma protect begin_protected\n";
  text.append(
      ProtectKeyBlockDirectives(request, content, kBlockKey, encoding, {}));
  text.append(ProtectDigestBlockDirectives(content, policy, encoding));
  text.append("`pragma protect end_protected\n");
  return text;
}

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

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

TEST(ProtectDigestDecryptKeyDescription, TheKeyTheBlockCarriesOpensTheDigest) {
  ReadUnderKeys run(
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kDigestSessionKey),
      TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyDescription,
     ADigestSealedUnderTheDataKeyDoesNotOpen) {
  ReadUnderKeys run(
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kSessionKey),
      TheBlockKey());
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyDescription,
     ADigestSealedUnderAStrangersKeyDoesNotOpen) {
  ReadUnderKeys run(
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kStrangersKey),
      TheBlockKey());
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyDescription, TheDigestBlockStandsOutsideTheKeyOne) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  EXPECT_NE(envelope.find("`pragma protect digest_block"), std::string::npos)
      << envelope;
}

TEST(ProtectDigestDecryptKeyDefault, ABlockCarryingNoneUsesTheDataKey) {
  ReadUnderKeys run(EnvelopeSealingItsDigestUnder({}, kSessionKey),
                    TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyDefault, ThatDefaultIsTheDataKeyAndNoOther) {
  ReadUnderKeys run(EnvelopeSealingItsDigestUnder({}, kStrangersKey),
                    TheBlockKey());
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyDefault, TheDataBlocksDigestOpensUnderTheDataKey) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  std::string data = ProtectEncodedValueDirective(
      encoding, ProtectedRegionBlockSize(kSealedDesign, kDataMethod));
  data.append("`pragma protect data_block\n");
  data.append(EncryptProtectedRegion(kSealedDesign, kSessionKey,
                                     encoding.enctype, kDataMethod));
  data.append("\n");
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(kSessionKey);
  data.append(ProtectDigestBlockDirectives(kSealedDesign, policy, encoding));
  std::string src = EnvelopeSealingItsDigestUnder({}, kSessionKey);
  src.insert(src.find("`pragma protect end_protected\n"), data);
  ReadUnderKeys run(src, TheBlockKey());
  EXPECT_TRUE(run.Holds("module sealed_m")) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

std::string ValueBeneath(std::string_view text, std::string_view keyword) {
  std::string opening = "`pragma protect ";
  opening.append(keyword).append("\n");
  size_t at = text.find(opening);
  if (at == std::string_view::npos) return {};
  size_t starts = at + opening.size();
  return std::string(text.substr(starts, text.find('\n', starts) - starts));
}

TEST(ProtectDigestDecryptKeyDefault, ARegionNamingNoneSealsItsDigestsLikeData) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  std::string key_block;
  ASSERT_TRUE(DecodeProtectBlock(
      BlockLinesAfter(envelope, "`pragma protect key_block\n"),
      DefaultProtectEncoding().enctype, &key_block))
      << envelope;
  std::string content;
  ASSERT_TRUE(DecryptProtectedBlock(key_block, kBlockKey, &content))
      << envelope;
  std::string data_key = ValueBeneath(content, "data_decrypt_key");
  ASSERT_FALSE(data_key.empty()) << content;
  EXPECT_EQ(ValueBeneath(content, "digest_decrypt_key"), data_key) << content;
}

TEST(ProtectDigestDecryptKeyDescription, AKeyTheAuthorMadeSealsTheDigest) {
  constexpr std::string_view kAuthorsKey = "the-authors-own-digest-key";
  std::string region = "`pragma protect digest_block\n`pragma protect begin\n";
  region.append(Writes("key_keyowner", kProvider));
  region.append(Writes("key_keyname", kBlockKeyName));
  region.append("`pragma protect digest_decrypt_key\n");
  region.append(EncodeProtectValue(kAuthorsKey, DefaultProtectEncoding()));
  region.append("\n").append(kSealedDesign).append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheBlockKey());
  size_t data_at = envelope.find("`pragma protect data_block\n");
  ASSERT_NE(data_at, std::string::npos) << envelope;
  constexpr std::string_view kDigestLine = "`pragma protect digest_block\n";
  size_t digest_at = envelope.find(kDigestLine, data_at);
  ASSERT_NE(digest_at, std::string::npos) << envelope;
  size_t starts = digest_at + kDigestLine.size();
  std::string encoded =
      envelope.substr(starts, envelope.find('\n', starts) - starts);
  std::string block;
  ASSERT_TRUE(
      DecodeProtectBlock(encoded, DefaultProtectEncoding().enctype, &block));
  std::string carried;
  EXPECT_TRUE(DecryptProtectedBlock(block, kAuthorsKey, &carried)) << envelope;
}

TEST(ProtectDigestDecryptKeyDefault, TheKeyOfAnEarlierEnvelopeIsNotCurrent) {
  std::string src =
      EnvelopeSealingItsDigestUnder(kDigestSessionKey, kDigestSessionKey);
  src += EnvelopeSealingItsDigestUnder({}, kSessionKey);
  ReadUnderKeys run(src, TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyEncryptionOutput, TheKeywordIsNowhereInTheClear) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  EXPECT_EQ(envelope.find("digest_decrypt_key"), std::string::npos) << envelope;
}

TEST(ProtectDigestDecryptKeyEncryptionOutput, TheCipherIsNotInTheClearEither) {
  std::string envelope = EnvelopeWithASignedKeyBlock();
  EXPECT_EQ(envelope.find(kDigestKeyMethod), std::string::npos) << envelope;
}

TEST(ProtectDigestDecryptKeyDecryptionInput,
     TheKeyBlockYieldsWhatOpensTheData) {
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), TheBlockKey());
  EXPECT_TRUE(run.Holds("module sealed_m")) << run.text;
}

TEST(ProtectDigestDecryptKeyDecryptionInput, TheDigestOpensUnderTheCarriedKey) {
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestDecryptKeyDecryptionInput, TheKeyBlockYieldsTheCipherToo) {
  ReadUnderKeys run(ThroughEndProtected(EnvelopeWithASignedKeyBlock()),
                    TheBlockKey());
  EXPECT_EQ(run.ValueOf("digest_key_method").value, kDigestKeyMethod);
}

TEST(ProtectDigestDecryptKeyDecryptionInput, AReaderWithoutTheKeyReachesNone) {
  ProtectKeyList strangers;
  strangers.Add(KeyOf(kProvider, kBlockKeyName, kStrangersKey));
  ReadUnderKeys run(EnvelopeWithASignedKeyBlock(), strangers);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

}  // namespace
