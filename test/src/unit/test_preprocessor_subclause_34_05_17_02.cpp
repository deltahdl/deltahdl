#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_block_lines.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_des.h"
#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

ProtectKeywordValue InEffectAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return ProtectDigestKeyMethodInEffect(pp.ProtectKeywords());
}

std::string StatesDataMethod(std::string_view value) {
  std::string text = "`pragma protect data_method=\"";
  text.append(value).append("\"\n");
  return text;
}

std::string StatesDigestKeyMethod(std::string_view value) {
  std::string text = "`pragma protect digest_key_method=\"";
  text.append(value).append("\"\n");
  return text;
}

TEST(ProtectDigestKeyMethodDescription, TheStatedAlgorithmStandsInEffect) {
  ProtectKeywordValue method = InEffectAfter(StatesDigestKeyMethod("rsa"));
  EXPECT_FALSE(method.defaulted);
  EXPECT_EQ(method.value, "rsa");
}

TEST(ProtectDigestKeyMethodDescription, TheDataCipherFillsThePlaceLeftEmpty) {
  ProtectKeywordValue method = InEffectAfter(StatesDataMethod("des-cbc"));
  EXPECT_TRUE(method.defaulted);
  EXPECT_EQ(method.value, "des-cbc");
}

TEST(ProtectDigestKeyMethodDescription, AnEmptyStringLeavesThePlaceEmpty) {
  std::string src = StatesDataMethod("des-cbc");
  src += StatesDigestKeyMethod("");
  ProtectKeywordValue method = InEffectAfter(src);
  EXPECT_TRUE(method.defaulted);
  EXPECT_EQ(method.value, "des-cbc");
}

TEST(ProtectDigestKeyMethodDescription,
     TheDataCipherDoesNotDisplaceAStatedOne) {
  std::string src = StatesDataMethod("des-cbc");
  src += StatesDigestKeyMethod("rsa");
  ProtectKeywordValue method = InEffectAfter(src);
  EXPECT_FALSE(method.defaulted);
  EXPECT_EQ(method.value, "rsa");
}

TEST(ProtectDigestKeyMethodDescription, StatingNeitherLeavesNoCipher) {
  ProtectKeywordValue method = InEffectAfter("`pragma protect author=\"a\"\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

TEST(ProtectDigestKeyMethodDescription, TheValuesAreTheOtherKeywordsValues) {
  EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier("des-cbc"));
  EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier("aes256-cbc"));
  EXPECT_FALSE(IsProtectDigestKeyMethodIdentifier("a-cipher-nobody-tabulated"));
}

constexpr std::string_view kSealedCore = "module ferrite_m; endmodule\n";

constexpr std::string_view kAuthorsExchangeKey = "the-authors-own-exchange-key";

constexpr std::string_view kTabulatedCipher = "twofish192-cbc";

constexpr std::string_view kCipherList = "(mode=\"ofb\", rounds=\"16\")";

std::string StatesDigestKeyMethodAsSpelled(std::string_view value) {
  std::string text = "`pragma protect digest_key_method=";
  text.append(value).append("\n");
  return text;
}

std::string EnvelopeStating(const std::string& described) {
  std::string region = "`pragma protect begin\n";
  region.append(described).append(kSealedCore);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedCore)) << envelope;
  EXPECT_FALSE(Holds(envelope, "key_block")) << envelope;
  return envelope;
}

TEST(ProtectDigestKeyMethodEncryptionOutput, AListNamesNoCipherOnTheEnvelope) {
  EXPECT_FALSE(
      Holds(EnvelopeStating(StatesDigestKeyMethodAsSpelled(kCipherList)),
            "digest_key_method"));
}

TEST(ProtectDigestKeyMethodEncryptionOutput,
     AStringNamesTheCipherTheEnvelopeStates) {
  EXPECT_TRUE(Holds(EnvelopeStating(StatesDigestKeyMethod(kTabulatedCipher)),
                    StatesDigestKeyMethod(kTabulatedCipher)));
}

TEST(ProtectDigestKeyMethodEncryptionOutput,
     AListLeavesTheStringBeforeItStanding) {
  std::string envelope =
      EnvelopeStating(StatesDigestKeyMethod(kTabulatedCipher) +
                      StatesDigestKeyMethodAsSpelled(kCipherList));
  EXPECT_TRUE(Holds(envelope, StatesDigestKeyMethod(kTabulatedCipher)))
      << envelope;
  EXPECT_FALSE(Holds(envelope, kCipherList)) << envelope;
}

constexpr std::string_view kDigestBlockLine = "`pragma protect digest_block\n";
constexpr std::string_view kDataBlockLine = "`pragma protect data_block\n";

std::string BlockBytesAfter(std::string_view envelope,
                            std::string_view opening) {
  std::string bytes;
  EXPECT_TRUE(ProtectBlockBytesAfter(envelope, opening, kBlockEnctype, &bytes))
      << envelope;
  return bytes;
}

std::string DesKeyOfTheExchangeKey() {
  std::string input(kAuthorsExchangeKey);
  input.append(4, '\0');
  return Sha1Digest(input).substr(0, kDesKeyBytes);
}

bool OpensUnderDesCbc(std::string_view bytes, std::string* digest) {
  if (bytes.size() <= kDesBlockBytes) return false;
  return DesCbcDecrypt(bytes.substr(kDesBlockBytes), DesKeyOfTheExchangeKey(),
                       bytes.substr(0, kDesBlockBytes), digest);
}

std::string SealedWithADigest(const std::string& described) {
  std::string region(described);
  region.append("`pragma protect begin\n");
  region.append(kDigestBlockLine).append(kSealedCore);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedCore)) << envelope;
  return envelope;
}

std::string DigestOfTheSealedText(std::string_view envelope) {
  std::string cleartext;
  EXPECT_TRUE(DecryptProtectedBlock(BlockBytesAfter(envelope, kDataBlockLine),
                                    kAuthorsExchangeKey, &cleartext,
                                    kDataMethod))
      << envelope;
  EXPECT_TRUE(Holds(cleartext, kSealedCore)) << cleartext;
  return Sha1Digest(cleartext);
}

void ExpectTheDigestUnderDesCbcAlone(std::string_view envelope) {
  std::string bytes = BlockBytesAfter(envelope, kDigestBlockLine);
  std::string digest;
  ASSERT_TRUE(OpensUnderDesCbc(bytes, &digest)) << envelope;
  EXPECT_EQ(digest, DigestOfTheSealedText(envelope)) << envelope;
  std::string under_stream;
  EXPECT_FALSE(DecryptProtectedBlock(bytes, kAuthorsExchangeKey, &under_stream,
                                     kDataMethod) &&
               under_stream == digest)
      << envelope;
}

TEST(ProtectDigestKeyMethodEncryptionInput,
     AStatedDesCbcSealsTheDigestUnderItBesideTheStreamCipher) {
  ExpectTheDigestUnderDesCbcAlone(SealedWithADigest(
      StatesDigestKeyMethod("des-cbc") + StatesDataMethod(kDataMethod)));
}

TEST(ProtectDigestKeyMethodEncryptionInput,
     AStatedDesCbcSealsTheDigestUnderItWithNoDataCipherStated) {
  ExpectTheDigestUnderDesCbcAlone(
      SealedWithADigest(StatesDigestKeyMethod("des-cbc")));
}

TEST(ProtectDigestKeyMethodEncryptionInput,
     AStatedStreamCipherSealsTheDigestUnderItBesideDesCbc) {
  std::string envelope = SealedWithADigest(StatesDigestKeyMethod(kDataMethod) +
                                           StatesDataMethod("des-cbc"));
  std::string bytes = BlockBytesAfter(envelope, kDigestBlockLine);
  std::string under_stream;
  ASSERT_TRUE(DecryptProtectedBlock(bytes, kAuthorsExchangeKey, &under_stream,
                                    kDataMethod))
      << envelope;
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedBlock(BlockBytesAfter(envelope, kDataBlockLine),
                                    kAuthorsExchangeKey, &cleartext, "des-cbc"))
      << envelope;
  EXPECT_EQ(under_stream, Sha1Digest(cleartext)) << envelope;
  std::string under_des;
  EXPECT_FALSE(OpensUnderDesCbc(bytes, &under_des) && under_des == under_stream)
      << envelope;
}

std::string WithADigestSealedElsewhereUnderDesCbc(const std::string& envelope) {
  const std::string kIv = "\x3c\xa1\x07\xe9\x52\x8d\x14\xf6";
  std::string sealed = kIv;
  sealed.append(DesCbcEncrypt(DigestOfTheSealedText(envelope),
                              DesKeyOfTheExchangeKey(), kIv));
  std::string rebuilt =
      WithProtectBlockBytes(envelope, kDigestBlockLine, sealed, kBlockEnctype);
  EXPECT_NE(rebuilt, envelope);
  return rebuilt;
}

ProtectDigestCheck DigestCheckReading(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_key = std::string(kAuthorsExchangeKey);
  Preprocessor pp(mgr, diag, config);
  std::string text = pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_TRUE(Holds(text, kSealedCore)) << text;
  return pp.LastDigestBlockCheck();
}

TEST(ProtectDigestKeyMethodDecryptionInput,
     ADigestSealedElsewhereUnderTheStatedDesCbcMatches) {
  std::string envelope =
      WithADigestSealedElsewhereUnderDesCbc(SealedWithADigest(
          StatesDigestKeyMethod("des-cbc") + StatesDataMethod(kDataMethod)));
  EXPECT_EQ(DigestCheckReading(envelope), ProtectDigestCheck::kMatched)
      << envelope;
}

TEST(ProtectDigestKeyMethodDecryptionInput,
     ADesCbcDigestUnderAnEnvelopeStatingTheStreamCipherDoesNotMatch) {
  std::string envelope =
      WithADigestSealedElsewhereUnderDesCbc(SealedWithADigest(
          StatesDigestKeyMethod("des-cbc") + StatesDataMethod(kDataMethod)));
  std::string stated = StatesDigestKeyMethod("des-cbc");
  size_t at = envelope.find(stated, envelope.find("begin_protected"));
  ASSERT_NE(at, std::string::npos) << envelope;
  envelope.replace(at, stated.size(), StatesDigestKeyMethod(kDataMethod));
  EXPECT_NE(DigestCheckReading(envelope), ProtectDigestCheck::kMatched)
      << envelope;
}

}  // namespace
