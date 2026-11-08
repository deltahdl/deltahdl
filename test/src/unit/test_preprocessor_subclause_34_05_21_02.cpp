#include <gtest/gtest.h>

#include <cstddef>
#include <span>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kStated = kMd5DigestMethod;
static_assert(kStated != kDefaultDigestMethod,
              "a region stating the identifier the default already supplies "
              "produces the envelope of a region that stated nothing");

constexpr std::string_view kIdentifierKeyword = "digest_method";

constexpr std::string_view kProvider = "meridian-trust";
constexpr std::string_view kBlockKeyName = "wrapping-2027";
constexpr std::string_view kBlockKey = "meridian-trust-wrapping-key";

constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kExchangeKey = "meridian-trust-author-key";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kDigestedText = "the bytes a digest stands in for";

constexpr std::string_view kDigestKey = "seals-the-digest-of-this-region";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

constexpr std::string_view kAListOfExpressions =
    "(rounds=\"64\", salt=\"none\")";

std::string WritesUnquoted(std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(kIdentifierKeyword).append("=").append(value).append("\n");
  return text;
}

std::string RequestsDigest() { return "`pragma protect digest_block\n"; }

std::string SignedRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kProvider));
  text.append(Writes("key_keyname", kBlockKeyName));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(described);
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

std::string UnsignedRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described);
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

ProtectKeyList TheBlockKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kProvider, kBlockKeyName, kBlockKey));
  return keys;
}

bool CarriesAGeneratedDigestBlock(const std::string& envelope) {
  size_t data = envelope.find("`pragma protect data_block\n");
  if (data == std::string::npos) return false;
  return envelope.find("`pragma protect digest_block", data) !=
         std::string::npos;
}

std::string SignedEnvelope(const std::string& described) {
  std::string envelope = EncryptEnvelopes(
      RequestsDigest() + SignedRegion(described), {}, TheBlockKey());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(envelope)) << envelope;
  return envelope;
}

std::string UnsignedEnvelope(const std::string& described) {
  std::string envelope = EncryptEnvelopes(
      RequestsDigest() + UnsignedRegion(described), kExchangeKey);
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(envelope)) << envelope;
  return envelope;
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

  ProtectKeywordValue Identifier() const {
    return ProtectDigestMethodInEffect(pp.ProtectKeywords());
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

TEST(ProtectDigestMethodTable, TheTableIsFourIdentifiersInTheOrderListed) {
  std::span<const ProtectDigestAlgorithm> rows = ProtectDigestAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  EXPECT_EQ(rows[0].identifier, "sha1");
  EXPECT_EQ(rows[1].identifier, "md5");
  EXPECT_EQ(rows[2].identifier, "md2");
  EXPECT_EQ(rows[3].identifier, "ripemd-160");
}

TEST(ProtectDigestMethodTable, TheTableRequiresTheFirstTwoIdentifiers) {
  EXPECT_TRUE(IsRequiredProtectDigestAlgorithm("sha1"));
  EXPECT_TRUE(IsRequiredProtectDigestAlgorithm("md5"));
}

TEST(ProtectDigestMethodTable, TheOtherTwoAreTabulatedWithoutBeingRequired) {
  EXPECT_TRUE(IsProtectDigestAlgorithm("md2"));
  EXPECT_FALSE(IsRequiredProtectDigestAlgorithm("md2"));
  EXPECT_TRUE(IsProtectDigestAlgorithm("ripemd-160"));
  EXPECT_FALSE(IsRequiredProtectDigestAlgorithm("ripemd-160"));
}

TEST(ProtectDigestMethodTable, EachRowNamesThePublishedAlgorithm) {
  std::span<const ProtectDigestAlgorithm> rows = ProtectDigestAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  EXPECT_NE(rows[0].algorithm.find("FIPS 180-2"), std::string_view::npos);
  EXPECT_NE(rows[1].algorithm.find("RFC 1321"), std::string_view::npos);
  EXPECT_NE(rows[2].algorithm.find("RFC 1319"), std::string_view::npos);
  EXPECT_NE(rows[3].algorithm.find("ISO/IEC 10118-3:2004"),
            std::string_view::npos);
}

TEST(ProtectDigestMethodTable, AnIdentifierOutsideTheTableIsNotTabulated) {
  EXPECT_FALSE(IsProtectDigestAlgorithm("sha256"));
}

TEST(ProtectDigestMethodTable, BeingTabulatedIsNotBeingProvided) {
  EXPECT_TRUE(IsProtectDigestAlgorithm("md2"));
  EXPECT_FALSE(ProtectDigestIsAvailable("md2"));
  EXPECT_TRUE(ProtectDigestIsAvailable("sha1"));
}

TEST(ProtectDigestMethodTable, TheDefaultIsAnIdentifierTheTableRequires) {
  EXPECT_TRUE(IsRequiredProtectDigestAlgorithm(kDefaultDigestMethod));
}

TEST(ProtectDigestMethodEncryptionInput, TwoIdentifiersGiveTwoDigests) {
  std::string under_sha1;
  std::string under_md5;
  ASSERT_TRUE(ProtectMessageDigest(kDigestedText, "sha1", &under_sha1));
  ASSERT_TRUE(ProtectMessageDigest(kDigestedText, "md5", &under_md5));
  EXPECT_NE(under_sha1, under_md5);
}

TEST(ProtectDigestMethodEncryptionInput,
     AnIdentifierWithNoAlgorithmHereGivesNothing) {
  std::string digest = "what the caller brought";
  EXPECT_FALSE(ProtectMessageDigest(kDigestedText, "md2", &digest));
  EXPECT_EQ(digest, "what the caller brought");
}

TEST(ProtectDigestMethodEncryptionInput,
     TheBlockWrittenIsTheIdentifiersDigest) {
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.key = std::string(kDigestKey);
  policy.method = "sha1";
  std::string under_sha1 = ProtectDigestBlockDirectives(
      kDigestedText, policy, DefaultProtectEncoding());
  policy.method = "md5";
  std::string under_md5 = ProtectDigestBlockDirectives(
      kDigestedText, policy, DefaultProtectEncoding());
  EXPECT_FALSE(under_sha1.empty());
  EXPECT_NE(under_sha1, under_md5);
}

TEST(ProtectDigestMethodEncryptionInput,
     AnIdentifierWithNoAlgorithmHereWritesNoBlock) {
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.key = std::string(kDigestKey);
  policy.method = "md2";
  EXPECT_EQ(ProtectDigestBlockDirectives(kDigestedText, policy,
                                         DefaultProtectEncoding()),
            "");
}

constexpr std::string_view kRequestedDesign = "module lattice_m; endmodule\n";
constexpr std::string_view kUnrequestedDesign = "module trellis_m; endmodule\n";
constexpr std::string_view kListingDesign = "module bezel_m; endmodule\n";

constexpr std::string_view kUnlistedIdentifier = "x-ferrule-fingerprint-64";

constexpr std::string_view kNoSuchDigest =
    "asks for a message digest algorithm this implementation does not "
    "provide: ";

constexpr std::string_view kTableLeavesItOptional =
    ", which IEEE 1800-2023 Table 34-4 does not require of every "
    "implementation";

std::string AsksForDigestUnder(std::string_view identifier) {
  std::string message(kNoSuchDigest);
  message.append(identifier).append(kTableLeavesItOptional);
  return message;
}

struct DigestingRun {
  PreprocFixture f;
  std::string text;

  explicit DigestingRun(const std::string& src)
      : text(EncryptEnvelopes(src, kExchangeKey, ProtectKeyList(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}
};

TEST(ProtectDigestMethodEncryptionInput,
     AnOptionalIdentifierAskedForIsReportedOnItsOwnLine) {
  std::string src = RequestsDigest();
  src += "`pragma protect begin\n";
  src.append(Writes(kIdentifierKeyword, kMd2DigestMethod));
  src.append(kRequestedDesign);
  src += "`pragma protect end\n";
  DigestingRun run(src);
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            AsksForDigestUnder(kMd2DigestMethod), 3,
                            "34.5.21.2"))
      << run.text;
}

TEST(ProtectDigestMethodEncryptionInput,
     AnUntabulatedIdentifierAskedForIsReported) {
  std::string src = Writes(kIdentifierKeyword, kUnlistedIdentifier);
  src += "module frame_m; endmodule\n";
  src.append(RequestsDigest());
  src += "`pragma protect begin\n";
  src += "  initial spindle = 5;\n";
  src += "`pragma protect end\n";
  DigestingRun run(src);
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            AsksForDigestUnder(kUnlistedIdentifier), 1,
                            "34.5.21.2"))
      << run.text;
}

TEST(ProtectDigestMethodEncryptionInput,
     AnAvailableIdentifierAskedForWritesItsBlockInSilence) {
  std::string src = "`pragma protect begin\n";
  src.append(Writes(kIdentifierKeyword, kMd5DigestMethod));
  src.append(RequestsDigest());
  src.append(kRequestedDesign);
  src += "`pragma protect end\n";
  DigestingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(run.text)) << run.text;
}

TEST(ProtectDigestMethodEncryptionInput,
     AnIdentifierNamedWithoutARequestIsNotReported) {
  std::string src = "`pragma protect begin\n";
  src.append(Writes(kIdentifierKeyword, kRipemd160DigestMethod));
  src.append(kUnrequestedDesign);
  src += "`pragma protect end\n";
  DigestingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_FALSE(CarriesAGeneratedDigestBlock(run.text)) << run.text;
}

TEST(ProtectDigestMethodEncryptionInput,
     NoIdentifierAskedForWritesItsBlockUnderTheDefault) {
  std::string src = RequestsDigest();
  src += "`pragma protect begin\n";
  src.append(kRequestedDesign);
  src += "`pragma protect end\n";
  DigestingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(run.text)) << run.text;
}

TEST(ProtectDigestMethodEncryptionInput,
     AListLeavesTheDefaultToComputeTheBlockUnder) {
  std::string src = "`pragma protect begin\n";
  src.append(WritesUnquoted(kAListOfExpressions));
  src.append(RequestsDigest());
  src.append(kListingDesign);
  src += "`pragma protect end\n";
  DigestingRun run(src);
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(run.text)) << run.text;
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
}

TEST(ProtectDigestMethodEncryptionOutput, AnUnsignedEnvelopeStatesItAsWritten) {
  std::string envelope = UnsignedEnvelope(Writes(kIdentifierKeyword, kStated));
  std::string directive = "`pragma protect digest_method=\"";
  directive.append(kStated).append("\"");
  EXPECT_NE(envelope.find(directive), std::string::npos) << envelope;
}

TEST(ProtectDigestMethodEncryptionOutput, ARegionStatingNoneGetsNone) {
  std::string envelope = UnsignedEnvelope("");
  EXPECT_EQ(envelope.find(kIdentifierKeyword), std::string::npos) << envelope;
}

TEST(ProtectDigestMethodEncryptionOutput, AListStatesNoAlgorithmOnTheEnvelope) {
  std::string envelope = UnsignedEnvelope(WritesUnquoted(kAListOfExpressions));
  EXPECT_EQ(envelope.find(kIdentifierKeyword), std::string::npos) << envelope;
}

TEST(ProtectDigestMethodEncryptionOutput,
     AListDoesNotUnstateTheAlgorithmBeforeIt) {
  std::string envelope = UnsignedEnvelope(Writes(kIdentifierKeyword, kStated) +
                                          WritesUnquoted(kAListOfExpressions));
  EXPECT_NE(envelope.find(Writes(kIdentifierKeyword, kStated)),
            std::string::npos)
      << envelope;
  EXPECT_EQ(envelope.find(kAListOfExpressions), std::string::npos) << envelope;
}

TEST(ProtectDigestMethodEncryptionOutput, ASignedEnvelopeKeepsItOutOfTheClear) {
  std::string envelope = SignedEnvelope(Writes(kIdentifierKeyword, kStated));
  EXPECT_EQ(envelope.find(kIdentifierKeyword), std::string::npos) << envelope;
}

TEST(ProtectDigestMethodDecryptionInput, TheKeyBlockYieldsTheIdentifier) {
  ReadUnderKeys run(
      ThroughEndProtected(SignedEnvelope(Writes(kIdentifierKeyword, kStated))),
      TheBlockKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_FALSE(run.Identifier().defaulted);
  EXPECT_EQ(run.Identifier().value, kStated);
}

TEST(ProtectDigestMethodDecryptionInput, AReaderWithoutTheKeyReachesNone) {
  ReadUnderKeys run(
      ThroughEndProtected(SignedEnvelope(Writes(kIdentifierKeyword, kStated))),
      ProtectKeyList());
  EXPECT_TRUE(run.Identifier().defaulted);
}

TEST(ProtectDigestMethodDecryptionInput, TheDigestAgreesUnderTheStatedOne) {
  ReadUnderKeys run(SignedEnvelope(Writes(kIdentifierKeyword, kStated)),
                    TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestMethodDecryptionInput, TheDigestAgreesUnderTheDefaultToo) {
  ReadUnderKeys run(ThroughEndProtected(SignedEnvelope("")), TheBlockKey());
  EXPECT_TRUE(run.Identifier().defaulted);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestMethodDecryptionInput, AnUnprovidedOneRegeneratesNoDigest) {
  std::string envelope = UnsignedEnvelope("");
  size_t block = envelope.find("`pragma protect digest_block",
                               envelope.find("`pragma protect data_block\n"));
  ASSERT_NE(block, std::string::npos);
  envelope.insert(block, Writes(kIdentifierKeyword, "md2"));
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, config);
  pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_EQ(pp.LastDigestBlockCheck(), ProtectDigestCheck::kUnreadable);
}

std::string LowercaseHex(std::string_view digest) {
  constexpr std::string_view kNibbles = "0123456789abcdef";
  std::string hex;
  for (char c : digest) {
    auto byte = static_cast<unsigned char>(c);
    hex.push_back(kNibbles[byte >> 4U]);
    hex.push_back(kNibbles[byte & 0x0FU]);
  }
  return hex;
}

TEST(ProtectDigestAlgorithms, Sha1GivesFips1802sExamples) {
  EXPECT_EQ(LowercaseHex(Sha1Digest("abc")),
            "a9993e364706816aba3e25717850c26c9cd0d89d");
  EXPECT_EQ(LowercaseHex(Sha1Digest(
                "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
            "84983e441c3bd26ebaae4aa1f95129e5e54670f1");
}

TEST(ProtectDigestAlgorithms, Md5GivesRfc1321sExamples) {
  EXPECT_EQ(LowercaseHex(Md5Digest("")), "d41d8cd98f00b204e9800998ecf8427e");
  EXPECT_EQ(LowercaseHex(Md5Digest("abc")), "900150983cd24fb0d6963f7d28e17f72");
  EXPECT_EQ(LowercaseHex(Md5Digest(
                "1234567890123456789012345678901234567890123456789012345678901"
                "2345678901234567890")),
            "57edf4a22be3c955ac49da2e2107b67a");
}

}  // namespace
