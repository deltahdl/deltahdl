#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_encoding.h"
#include "helpers_protect_block_lines.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kFirstProvider = "meridian-trust";
constexpr std::string_view kFirstKeyName = "wrapping-2026";
constexpr std::string_view kFirstKey = "meridian-trust-wrapping-key";
constexpr std::string_view kSecondProvider = "cerulean-vault";
constexpr std::string_view kSecondKeyName = "wrapping-2027";
constexpr std::string_view kSecondKey = "cerulean-vault-wrapping-key";

constexpr std::string_view kLongDigestKey =
    "meridian-trust-digest-sealing-key-of-2026";

constexpr std::string_view kDataKeyName = "design-2026";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Designates(std::string_view provider, std::string_view key_name) {
  std::string text = Writes("key_keyowner", provider);
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(Writes("key_keyname", key_name));
  return text;
}

ProtectKeyList KeysOfBothProviders() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstProvider, kFirstKeyName, kFirstKey));
  keys.Add(KeyOf(kSecondProvider, kSecondKeyName, kSecondKey));
  return keys;
}

std::string TwoKeyBlockEnvelope(std::string_view asked) {
  std::string described(asked);
  described.append(Designates(kFirstProvider, kFirstKeyName));
  described.append(Designates(kSecondProvider, kSecondKeyName));
  std::string envelope =
      EncryptEnvelopes(RegionHolding(described), {}, KeysOfBothProviders());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  return envelope;
}

bool Opens(const std::string& line, std::string_view keyword) {
  std::string opening = "`pragma protect ";
  opening.append(keyword);
  return line.rfind(opening, 0) == 0;
}

std::vector<std::string> BlocksOf(const std::string& envelope) {
  std::vector<std::string> blocks;
  for (const std::string& line : AllLines(envelope)) {
    if (Opens(line, "key_block")) {
      blocks.emplace_back("key");
    } else if (Opens(line, "data_block")) {
      blocks.emplace_back("data");
    } else if (Opens(line, "digest_block")) {
      blocks.emplace_back("digest");
    }
  }
  return blocks;
}

ProtectEncoding TheScheme() { return DefaultProtectEncoding(); }

std::string DigestOf(std::string_view cleartext) {
  std::string digest;
  EXPECT_TRUE(ProtectMessageDigest(cleartext, kDefaultDigestMethod, &digest))
      << cleartext;
  return digest;
}

std::string DataBlockHolding(std::string_view sealed) {
  std::string text = ProtectEncodedValueDirective(
      TheScheme(), ProtectedRegionBlockSize(sealed));
  text.append(kEncodingBlockOpening);
  text.append(EncryptProtectedRegion(sealed, kEncodingExchangeKey,
                                     TheScheme().enctype));
  text.push_back('\n');
  return text;
}

std::string DigestBlockUnder(std::string_view vouched_for,
                             std::string_view key) {
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(key);
  return ProtectDigestBlockDirectives(vouched_for, policy, TheScheme());
}

std::string DigestBlockVouchingFor(std::string_view vouched_for) {
  return DigestBlockUnder(vouched_for, kEncodingExchangeKey);
}

std::string EnvelopeCarrying(const std::string& described) {
  std::string text(kProtectedOpening);
  text.push_back('\n');
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, HoldingTheKey()};
  std::string text;

  explicit ReadEnvelope(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

TEST(ProtectDigestBlockEncryptionInput, ARequestOutsideAProtectedBlockAsks) {
  EXPECT_TRUE(Holds(TwoKeyBlockEnvelope(kDigestBlockLine), kDigestBlockLine));
}

TEST(ProtectDigestBlockEncryptionInput, ARequestInsideAProtectedBlockAsksNot) {
  std::string source = EnvelopeCarrying(std::string(kDigestBlockLine));
  source.append(RegionHolding(Designates(kFirstProvider, kFirstKeyName) +
                              Designates(kSecondProvider, kSecondKeyName)));
  std::string produced = EncryptEnvelopes(source, {}, KeysOfBothProviders());
  EXPECT_FALSE(Holds(produced, kEncodingSealedDesign)) << produced;
  EXPECT_EQ(TimesWritten(produced, kDigestBlockLine), 1U) << produced;
}

TEST(ProtectDigestBlockEncryptionInput, ARequestInsideTheRegionStaysOutOfIt) {
  constexpr std::string_view kDesign = "module asked_inside_m; endmodule\n";
  std::string source = "`pragma protect begin\n";
  source.append(kDigestBlockLine).append(kDesign);
  source.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(source, kEncodingExchangeKey);
  ReadEnvelope run(envelope);
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kDesign)) << envelope;
  EXPECT_FALSE(Holds(run.text, kDigestBlockLine)) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched) << envelope;
}

TEST(ProtectDigestBlockEncryptionOutput, EachBlockGeneratedGetsItsOwnDigest) {
  EXPECT_EQ(BlocksOf(TwoKeyBlockEnvelope(kDigestBlockLine)),
            (std::vector<std::string>{"key", "digest", "key", "digest", "data",
                                      "digest"}));
}

TEST(ProtectDigestBlockEncryptionOutput, TheDigestIsUnderTheRegionsDataCipher) {
  constexpr std::string_view kDesign = "module vouched_m; endmodule\n";
  std::string source = "`pragma protect data_method=\"des-cbc\"\n";
  source.append("`pragma protect digest_block\n`pragma protect begin\n");
  source.append(kDesign).append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(source, kEncodingExchangeKey);
  std::string after_data =
      envelope.substr(envelope.find(kEncodingBlockOpening));
  std::string digest_block;
  ASSERT_TRUE(DecodeProtectBlock(BlockLinesAfter(after_data, kDigestBlockLine),
                                 TheScheme().enctype, &digest_block))
      << envelope;
  std::string carried;
  ASSERT_TRUE(DecryptProtectedBlock(digest_block, kEncodingExchangeKey,
                                    &carried, kDesCbcMethod))
      << envelope;
  EXPECT_EQ(carried, DigestOf(kDesign));
  ReadEnvelope run(envelope);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestBlockEncryptionOutput, ARegionAskingForNoneGetsNoneAtAll) {
  EXPECT_EQ(BlocksOf(TwoKeyBlockEnvelope("")),
            (std::vector<std::string>{"key", "key", "data"}));
}

TEST(ProtectDigestBlockEncryptionOutput, NoKeyReachedWritesNoDigest) {
  EXPECT_EQ(DigestBlockUnder(kEncodingSealedDesign, ""), "");
  EXPECT_NE(DigestBlockUnder(kEncodingSealedDesign, kEncodingExchangeKey), "");
}

TEST(ProtectDigestBlockEncryptionOutput, TheLineHoldsTheDigestAndNothingElse) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  std::string carried;
  ASSERT_TRUE(DecodeProtectBlock(LineAfter(envelope, kDigestBlockLine),
                                 TheScheme().enctype, &carried))
      << envelope;
  std::string opened;
  ASSERT_TRUE(DecryptProtectedBlock(carried, kEncodingExchangeKey, &opened))
      << envelope;
  EXPECT_EQ(opened, DigestOf(kEncodingSealedDesign));
}

TEST(ProtectDigestBlockEncryptionOutput, TheDigestIsCountedAsAValueOfItsOwn) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  EXPECT_TRUE(Holds(envelope, TheCountOf(ProtectedRegionBlockSize(
                                  DigestOf(kEncodingSealedDesign)))))
      << envelope;
}

TEST(ProtectDigestBlockDecryptionInput, ADigestOfTheBlockItFollowsAgrees) {
  ReadEnvelope run(
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kEncodingSealedDesign)));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestBlockDecryptionInput, ADigestOnSeveralLinesStillAgrees) {
  std::string src =
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kEncodingSealedDesign));
  std::string broken = WithBlockBrokenIntoLines(src, kDigestBlockLine, 3);
  ASSERT_NE(broken, src);

  ReadEnvelope run(broken);
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestBlockDecryptionInput, ADigestOfOtherTextIsReported) {
  std::string src = EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                                     DigestBlockVouchingFor(kSecondDesign));
  ReadEnvelope run(src);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kAltered);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "digest block disagrees with the block it follows",
                            LineHolding(src, LineAfter(src, kDigestBlockLine)),
                            "34.5.22"));
}

TEST(ProtectDigestBlockDecryptionInput, ADigestNotInTheSchemeChecksNothing) {
  std::string src =
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                       std::string(kDigestBlockLine) + "not a block\n");
  ReadEnvelope run(src);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma value is not written in the encoding in effect",
      LineHolding(src, "not a block"), "34.5.9.2"));
}

TEST(ProtectDigestBlockDecryptionInput, ADirectiveAfterTheKeywordIsNoDigest) {
  ReadEnvelope run(EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                                    std::string(kDigestBlockLine) +
                                    "`pragma protect author=\"after\"\n"));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

TEST(ProtectDigestBlockDecryptionInput, ASecondDigestFollowsNoBlockOfItsOwn) {
  ReadEnvelope run(
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kSecondDesign)));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestBlockDecryptionInput,
     ADigestReachesNoBlockOfAnotherEnvelope) {
  ReadEnvelope run(
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign)) +
      EnvelopeCarrying(DigestBlockVouchingFor(kEncodingSealedDesign)));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

TEST(ProtectDigestBlockDecryptionInput,
     AKeyMatchingTheDigestBlocksLengthReadsNothing) {
  const std::string kSealedDigest = DigestOf(kEncodingSealedDesign);
  const size_t kBlockBytes = ProtectedRegionBlockSize(kSealedDigest);
  ASSERT_GE(kLongDigestKey.size(), kBlockBytes);
  const std::string kImpostorKey =
      std::string(kLongDigestKey.substr(0, kBlockBytes)) + "-impostor";
  ASSERT_EQ(kImpostorKey.substr(0, kBlockBytes),
            std::string(kLongDigestKey.substr(0, kBlockBytes)));
  ASSERT_NE(kImpostorKey, std::string(kLongDigestKey));
  std::string written = DigestBlockUnder(kEncodingSealedDesign, kLongDigestKey);
  std::string block;
  ASSERT_TRUE(DecodeProtectBlock(LineAfter(written, kDigestBlockLine),
                                 TheScheme().enctype, &block))
      << written;
  ProtectDigestTarget target;
  target.cleartext = std::string(kEncodingSealedDesign);
  target.key = std::string(kLongDigestKey);
  EXPECT_EQ(CheckProtectDigestBlock(block, target, kDefaultDigestMethod),
            ProtectDigestCheck::kMatched);
  target.key = kImpostorKey;
  EXPECT_EQ(CheckProtectDigestBlock(block, target, kDefaultDigestMethod),
            ProtectDigestCheck::kUnreadable);
}

}  // namespace
