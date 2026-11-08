#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_des.h"
#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kRegionKey = "one-key-of-the-authors-own";

constexpr std::string_view kNotProvided =
    "states an encryption algorithm this implementation does not provide";

std::string OurEnvelope() {
  std::string region = "`pragma protect begin\n";
  region.append(kSealedDesign);
  region += "`pragma protect end\n";
  std::string envelope = EncryptEnvelopes(region, std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

std::string EnvelopeUnderDesCbc() {
  std::string region = "`pragma protect begin\n";
  region += "`pragma protect data_method=\"";
  region.append(kDesCbcMethod).append("\"\n");
  region.append(kSealedDesign);
  region += "`pragma protect end\n";
  std::string envelope = EncryptEnvelopes(region, std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

std::string EnvelopeNaming(std::string_view identifier) {
  std::string envelope = OurEnvelope();
  std::string ours = "`pragma protect data_method=\"";
  ours.append(kDataMethod).append("\"");
  auto at = envelope.find(ours);
  EXPECT_NE(at, std::string::npos) << envelope;
  if (at == std::string::npos) return envelope;
  std::string theirs = "`pragma protect data_method=\"";
  theirs.append(identifier).append("\"");
  return envelope.replace(at, ours.size(), theirs);
}

struct ReadBack {
  PreprocFixture f;
  std::string source;
  std::string text;

  explicit ReadBack(const std::string& src) : source(src) {
    PreprocConfig config;
    config.protect_key = std::string(kRegionKey);
    text = Preprocess(src, f, config);
  }

  bool Recovered() const {
    return text.find(kSealedDesign) != std::string::npos;
  }
};

uint32_t TheCipheredBlocksLine(std::string_view envelope) {
  return LineHolding(envelope, "`pragma protect data_block\n") + 1;
}

TEST(ProtectDataMethodDescription, ABlockNamingTheRequiredCipherIsOpened) {
  ReadBack run(EnvelopeUnderDesCbc());
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Recovered()) << run.text;
}

TEST(ProtectDataMethodDescription,
     ABlockNamingAnOptionalCipherWeLackIsReported) {
  ReadBack run(EnvelopeNaming("aes128-cbc"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            TheCipheredBlocksLine(run.source), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

TEST(ProtectDataMethodDescription, ABlockNamingAnUnknownIdentifierIsReported) {
  ReadBack run(EnvelopeNaming("x-some-other-tools-cipher"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            TheCipheredBlocksLine(run.source), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

TEST(ProtectDataMethodDescription, ABlockNamingTheCipherWeProvideIsRead) {
  ReadBack run(OurEnvelope());
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_TRUE(run.Recovered()) << run.text;
}

TEST(ProtectDataMethodDescription, AnEmptyIdentifierNamesNoAlgorithm) {
  ReadBack run(EnvelopeNaming(""));
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Recovered()) << run.text;
}

constexpr std::string_view kBlockProvider = "meridian-trust";
constexpr std::string_view kBlockProviderName = "wrapping-2029";
constexpr std::string_view kBlockProviderKey = "meridian-trust-wrapping-key";

constexpr std::string_view kDataProvider = "kestrel-systems";
constexpr std::string_view kDataProviderName = "kestrel-data-2029";
constexpr std::string_view kDataProviderKey = "kestrel-region-exchange-key";

constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

constexpr std::string_view kMethodDirective = "`pragma protect data_method=";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string StatesTheCipherWeProvide() {
  return Writes(kDataMethodKeyword, kDataMethod);
}

std::string RegionNamingBothProviders() {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kDataProvider));
  text.append(Writes("data_keyname", kDataProviderName));
  text.append(Writes("key_keyowner", kBlockProvider));
  text.append(Writes("key_keyname", kBlockProviderName));
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

std::string RegionNamingTheDataProviderAlone() {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kDataProvider));
  text.append(Writes("data_keyname", kDataProviderName));
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

ProtectKeyList OnlyTheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  return keys;
}

ProtectKeyList BothProvidersKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockProviderName, kBlockProviderKey));
  keys.Add(KeyOf(kDataProvider, kDataProviderName, kDataProviderKey));
  return keys;
}

TEST(ProtectDataMethodEncryptionOutput,
     TheCipherLeavesTheClearWhereAKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_FALSE(Holds(envelope, kMethodDirective)) << envelope;
}

TEST(ProtectDataMethodEncryptionOutput,
     TheCipherStandsInTheClearWhereNoKeyBlockCarriesIt) {
  std::string envelope = EncryptEnvelopes(RegionNamingTheDataProviderAlone(),
                                          {}, BothProvidersKeys());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 0U) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, StatesTheCipherWeProvide())) << envelope;
}

TEST(ProtectDataMethodEncryptionOutput,
     TheCipherInTheBlockStillOpensTheRegion) {
  std::string envelope = EncryptEnvelopes(RegionNamingBothProviders(), {},
                                          OnlyTheBlockProvidersKey());
  PreprocFixture f;
  PreprocConfig config;
  config.protect_keys = OnlyTheBlockProvidersKey();
  std::string read = Preprocess(envelope, f, config);
  EXPECT_FALSE(f.diag.HasErrors()) << read;
  EXPECT_TRUE(Holds(read, kSealedDesign)) << read;
}

constexpr std::string_view kAskedDesign = "module gasket_m; endmodule\n";
constexpr std::string_view kAskingKey = "another-key-of-the-authors-own";

constexpr std::string_view kUnaskedDesign = "module cradle_m; endmodule\n";

constexpr std::string_view kNoSuchCipher =
    "asks for an encryption algorithm this implementation does not provide: ";

constexpr std::string_view kTableAdmitsWithoutRequiring =
    ", which IEEE 1800-2023 Table 34-3 does not require of every "
    "implementation";

std::string AsksFor(std::string_view identifier, std::string_view tabulated) {
  std::string message(kNoSuchCipher);
  message.append(identifier).append(tabulated);
  return message;
}

struct SealingRun {
  PreprocFixture f;
  std::string text;

  explicit SealingRun(const std::string& src)
      : text(EncryptEnvelopes(src, kAskingKey, ProtectKeyList(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}

  bool Sealed(std::string_view design) const {
    return !Holds(text, design) && Holds(text, kDataBlockKeyword);
  }
};

TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForTheRequiredCipherIsSealedUnderIt) {
  std::string src = "`pragma protect begin\n";
  src.append(Writes(kDataMethodKeyword, kDesCbcMethod));
  src.append(kAskedDesign);
  src += "`pragma protect end\n";
  SealingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Sealed(kAskedDesign)) << run.text;
  EXPECT_TRUE(Holds(run.text, Writes(kDataMethodKeyword, kDesCbcMethod)))
      << run.text;
  EXPECT_FALSE(Holds(run.text, Writes(kDataMethodKeyword, kDataMethod)))
      << run.text;
}

TEST(ProtectDataMethodEncryptionInput, TwoEnvelopesOfOneRegionCarryTheirOwnIv) {
  std::string first = EnvelopeUnderDesCbc();
  std::string second = EnvelopeUnderDesCbc();
  EXPECT_NE(first, second);

  ReadBack opened_first(first);
  ReadBack opened_second(second);
  EXPECT_TRUE(opened_first.Recovered()) << opened_first.text;
  EXPECT_TRUE(opened_second.Recovered()) << opened_second.text;
}

TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForAnOptionalCipherSaysTheTableDoesNotRequireIt) {
  std::string src = "module bezel_m;\n`pragma protect begin\n";
  src.append(Writes(kDataMethodKeyword, "aes256-cbc"));
  src += "  initial hatch = 7;\n`pragma protect end\nendmodule\n";
  SealingRun run(src);
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            AsksFor("aes256-cbc", kTableAdmitsWithoutRequiring),
                            3, "34.5.11.2"))
      << run.text;
}

TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForTheCipherWeProvideIsSealedInSilence) {
  std::string src = "`pragma protect begin\n";
  src.append(StatesTheCipherWeProvide());
  src.append(kAskedDesign);
  src += "`pragma protect end\n";
  SealingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Sealed(kAskedDesign)) << run.text;
}

TEST(ProtectDataMethodEncryptionInput,
     ARegionAskingForNoCipherIsSealedInSilence) {
  std::string src = "`pragma protect begin\n";
  src.append(kUnaskedDesign);
  src += "`pragma protect end\n";
  SealingRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Sealed(kUnaskedDesign)) << run.text;
}

TEST(ProtectDataMethodEncryptionInput,
     ACipherNamedAheadOfTheRegionIsReportedOnItsOwnLine) {
  std::string src = Writes(kDataMethodKeyword, "blowfish-cbc");
  src += "module bracket_m; endmodule\n`pragma protect begin\n";
  src += "  initial latch = 3;\n`pragma protect end\n";
  SealingRun run(src);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      AsksFor("blowfish-cbc", kTableAdmitsWithoutRequiring), 1, "34.5.11.2"))
      << run.text;
}

std::string BytesOfHex(std::string_view hex) {
  std::string bytes;
  for (size_t at = 0; at + 1 < hex.size(); at += 2) {
    unsigned value = 0;
    for (size_t n = 0; n < 2; ++n) {
      char c = hex[at + n];
      unsigned digit = c <= '9' ? static_cast<unsigned>(c - '0')
                                : static_cast<unsigned>(c - 'A' + 10);
      value = (value << 4) | digit;
    }
    bytes.push_back(static_cast<char>(value));
  }
  return bytes;
}

std::string HexOfBytes(std::string_view bytes) {
  constexpr std::string_view kDigits = "0123456789ABCDEF";
  std::string hex;
  for (char c : bytes) {
    auto byte = static_cast<uint8_t>(c);
    hex.push_back(kDigits[byte >> 4]);
    hex.push_back(kDigits[byte & 0xFU]);
  }
  return hex;
}

void ExpectDesVector(std::string_view key_hex, std::string_view plain_hex,
                     std::string_view cipher_hex) {
  std::string key = BytesOfHex(key_hex);
  std::string plain = BytesOfHex(plain_hex);
  std::string ciphered = DesEncryptBlock(plain, key);
  EXPECT_EQ(HexOfBytes(ciphered), cipher_hex);
  EXPECT_EQ(HexOfBytes(DesDecryptBlock(BytesOfHex(cipher_hex), key)),
            plain_hex);
}

TEST(ProtectDataMethodCipher, TheWorkedExampleVectorIsAnswered) {
  ExpectDesVector("133457799BBCDFF1", "0123456789ABCDEF", "85E813540F0AB405");
}

TEST(ProtectDataMethodCipher, TheZeroCiphertextVectorIsAnswered) {
  ExpectDesVector("0E329232EA6D0D73", "8787878787878787", "0000000000000000");
}

TEST(ProtectDataMethodCipher, TheZeroKeyAndZeroBlockVectorIsAnswered) {
  ExpectDesVector("0000000000000000", "0000000000000000", "8CA64DE9C1B123A7");
}

TEST(ProtectDataMethodCipher, ChainingMakesTwoLikeBlocksDiffer) {
  const std::string kKey = BytesOfHex("133457799BBCDFF1");
  const std::string kIv = BytesOfHex("0011223344556677");
  const std::string kText = "abcdefghabcdefgh";
  std::string ciphered = DesCbcEncrypt(kText, kKey, kIv);
  ASSERT_GE(ciphered.size(), 2 * kDesBlockBytes);
  EXPECT_NE(ciphered.substr(0, kDesBlockBytes),
            ciphered.substr(kDesBlockBytes, kDesBlockBytes));

  std::string recovered;
  ASSERT_TRUE(DesCbcDecrypt(ciphered, kKey, kIv, &recovered));
  EXPECT_EQ(recovered, kText);
}

TEST(ProtectDataMethodCipher, ADifferentKeyDoesNotGiveTheTextBack) {
  const std::string kIv = BytesOfHex("0011223344556677");
  const std::string kText = "module m; endmodule\n";
  std::string ciphered =
      DesCbcEncrypt(kText, BytesOfHex("133457799BBCDFF1"), kIv);
  ASSERT_FALSE(ciphered.empty());

  std::string recovered;
  bool opened =
      DesCbcDecrypt(ciphered, BytesOfHex("133457799BBCDFF5"), kIv, &recovered);
  EXPECT_FALSE(opened && recovered == kText);
}

TEST(ProtectDataMethodCipher, ABlockOrKeyOfAnotherLengthGivesNothing) {
  const std::string kKey = BytesOfHex("133457799BBCDFF1");
  const std::string kBlock = BytesOfHex("0123456789ABCDEF");
  EXPECT_EQ(DesEncryptBlock(kBlock.substr(1), kKey), "");
  EXPECT_EQ(DesEncryptBlock(kBlock, kKey.substr(1)), "");
  EXPECT_EQ(DesDecryptBlock(kBlock, kKey.substr(1)), "");
}

TEST(ProtectDataMethodCipher, AKeyOrIvOfAnotherLengthChainsNothing) {
  const std::string kKey = BytesOfHex("133457799BBCDFF1");
  const std::string kIv = BytesOfHex("0011223344556677");
  const std::string kText = "abcdefgh";
  EXPECT_EQ(DesCbcEncrypt(kText, kKey.substr(1), kIv), "");
  EXPECT_EQ(DesCbcEncrypt(kText, kKey, kIv.substr(1)), "");
  std::string ciphered = DesCbcEncrypt(kText, kKey, kIv);
  std::string recovered;
  EXPECT_FALSE(DesCbcDecrypt(ciphered, kKey.substr(1), kIv, &recovered));
  EXPECT_FALSE(DesCbcDecrypt(ciphered, kKey, kIv.substr(1), &recovered));
}

TEST(ProtectDataMethodCipher, CiphertextThatIsNotWholeBlocksIsRefused) {
  const std::string kKey = BytesOfHex("133457799BBCDFF1");
  const std::string kIv = BytesOfHex("0011223344556677");
  std::string ciphered = DesCbcEncrypt("abcdefgh", kKey, kIv);
  std::string recovered;
  EXPECT_FALSE(DesCbcDecrypt("", kKey, kIv, &recovered));
  EXPECT_FALSE(DesCbcDecrypt(ciphered.substr(0, kDesBlockBytes + 1), kKey, kIv,
                             &recovered));
}

TEST(ProtectDataMethodCipher, PaddingThisNeverWritesIsRefused) {
  const std::string kKey = BytesOfHex("133457799BBCDFF1");
  const std::string kZeroIv(kDesBlockBytes, '\0');
  std::string recovered;
  for (std::string_view block :
       {std::string_view("abcdefg\0", 8), std::string_view("abcdefg\x09"),
        std::string_view("abcdefg\x02")}) {
    EXPECT_FALSE(
        DesCbcDecrypt(DesEncryptBlock(block, kKey), kKey, kZeroIv, &recovered))
        << HexOfBytes(block);
  }
  ASSERT_TRUE(DesCbcDecrypt(DesEncryptBlock("abcdef\x02\x02", kKey), kKey,
                            kZeroIv, &recovered));
  EXPECT_EQ(recovered, "abcdef");
}

TEST(ProtectDataMethodCipher, ABlockNoLongerThanItsIvRecordsNoRegion) {
  std::string block = EncryptProtectedRegion(kSealedDesign, kRegionKey,
                                             kRawEnctype, kDesCbcMethod);
  ASSERT_GT(block.size(), kDesBlockBytes);
  std::string recovered;
  EXPECT_TRUE(
      DecryptProtectedBlock(block, kRegionKey, &recovered, kDesCbcMethod));
  EXPECT_FALSE(DecryptProtectedBlock(block.substr(0, kDesBlockBytes),
                                     kRegionKey, &recovered, kDesCbcMethod));
}

TEST(ProtectDataMethodCipher, AnEmptyKeyEncryptsNothing) {
  EXPECT_EQ(EncryptProtectedRegion(kSealedDesign, ""), "");
  EXPECT_EQ(
      EncryptProtectedRegion(kSealedDesign, "", kRawEnctype, kDesCbcMethod),
      "");
}

TEST(ProtectDataMethodCipher, ADesCbcBlockRecordsTheRegionAlone) {
  std::string block =
      EncryptProtectedRegion("abcd", kRegionKey, kRawEnctype, kDesCbcMethod);
  EXPECT_EQ(block.size(), 2 * kDesBlockBytes);
  EXPECT_EQ(ProtectedRegionBlockSize("abcd", kDesCbcMethod),
            2 * kDesBlockBytes);
  std::string recovered;
  ASSERT_TRUE(
      DecryptProtectedBlock(block, kRegionKey, &recovered, kDesCbcMethod));
  EXPECT_EQ(recovered, "abcd");
}

TEST(ProtectDataMethodCipher, ADesCbcBlockWithoutAPrefixIsOpened) {
  std::string counter(4, '\0');
  std::string des_key = Sha1Digest(std::string(kRegionKey) + counter);
  des_key.resize(kDesKeyBytes);
  const std::string kIv = "\x13\x57\x9b\xdf\x02\x46\x8a\xce";
  std::string block = kIv + DesCbcEncrypt(kSealedDesign, des_key, kIv);
  std::string recovered;
  ASSERT_TRUE(
      DecryptProtectedBlock(block, kRegionKey, &recovered, kDesCbcMethod));
  EXPECT_EQ(recovered, kSealedDesign);
}

}  // namespace
