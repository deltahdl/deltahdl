#include <gtest/gtest.h>

#include <cstddef>
#include <span>
#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kEntityKey = "meridian-trust-wrapping-key";

constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kKeyCipher = "des-cbc";
constexpr std::string_view kDigestAlgorithm = "md5";

constexpr std::string_view kOptionalCipher = "aes256-cbc";

constexpr std::string_view kProvidedCipher = kDataMethod;

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kUnblockedCipher = "cast128-cbc";

constexpr std::string_view kDirectEntity = "harbour-labs";
constexpr std::string_view kDirectKeyName = "direct-2028";
constexpr std::string_view kDirectKey = "harbour-labs-direct-key";

constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

constexpr std::string_view kKeyMethodDirective = "`pragma protect key_method=";

constexpr std::string_view kNoCipherOfOurs =
    "protect pragma key_method asks for an encryption algorithm this "
    "implementation does not provide: ";

constexpr std::string_view kTableLeavesItOptional =
    ", which IEEE 1800-2023 Table 34-3 does not require of every "
    "implementation";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

ProtectKeyList TheEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kEntityKey));
  return keys;
}

std::string SignedRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kEntity));
  text.append(Writes("key_keyname", kKeyName));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

std::string SignedEnvelope(const std::string& described) {
  std::string envelope =
      EncryptEnvelopes(SignedRegion(described), {}, TheEntitysKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  return envelope;
}

std::string ReadBack(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheEntitysKey();
  Preprocessor pp(mgr, diag, std::move(config));
  return pp.Preprocess(mgr.AddFile("<test>", envelope));
}

std::string AskingFor(std::string_view identifier, std::string_view tabulated) {
  std::string message(kNoCipherOfOurs);
  message.append(identifier).append(tabulated);
  return message;
}

ProtectKeyList TheDirectEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kDirectEntity, kDirectKeyName, kDirectKey));
  return keys;
}

std::string DirectRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kDirectEntity));
  text.append(Writes("data_keyname", kDirectKeyName));
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

struct AuthorsRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string envelope;

  AuthorsRun(const std::string& source, const ProtectKeyList& keys)
      : envelope(EncryptEnvelopes(source, {}, keys, &diag,
                                  mgr.AddFile("<test>", source))) {}
};

std::string_view IdentifierStatedFor(std::string_view envelope,
                                     std::string_view keyword) {
  std::string directive = "`pragma protect ";
  directive.append(keyword).append("=");
  size_t at = envelope.find(directive);
  if (at == std::string_view::npos) return {};
  size_t from = at + directive.size();
  size_t end = envelope.find('\n', from);
  return ProtectPragmaValueBody(envelope.substr(from, end - from));
}

TEST(ProtectKeyMethodDescription,
     TheTableIsSixteenIdentifiersInTheOrderListed) {
  std::span<const ProtectEncryptionAlgorithm> rows =
      ProtectEncryptionAlgorithms();
  ASSERT_EQ(rows.size(), 16U);
  EXPECT_EQ(rows[0].identifier, "des-cbc");
  EXPECT_EQ(rows[1].identifier, "3des-cbc");
  EXPECT_EQ(rows[2].identifier, "aes128-cbc");
  EXPECT_EQ(rows[3].identifier, "aes256-cbc");
  EXPECT_EQ(rows[4].identifier, "aes192-cbc");
  EXPECT_EQ(rows[5].identifier, "blowfish-cbc");
  EXPECT_EQ(rows[6].identifier, "twofish256-cbc");
  EXPECT_EQ(rows[7].identifier, "twofish192-cbc");
  EXPECT_EQ(rows[8].identifier, "twofish128-cbc");
  EXPECT_EQ(rows[9].identifier, "serpent256-cbc");
  EXPECT_EQ(rows[10].identifier, "serpent192-cbc");
  EXPECT_EQ(rows[11].identifier, "serpent128-cbc");
  EXPECT_EQ(rows[12].identifier, "cast128-cbc");
  EXPECT_EQ(rows[13].identifier, "rsa");
  EXPECT_EQ(rows[14].identifier, "elgamal");
  EXPECT_EQ(rows[15].identifier, "pgp-rsa");
}

TEST(ProtectKeyMethodDescription,
     OneIdentifierIsRequiredOfEveryImplementation) {
  std::span<const ProtectEncryptionAlgorithm> rows =
      ProtectEncryptionAlgorithms();
  ASSERT_EQ(rows.size(), 16U);
  EXPECT_TRUE(IsRequiredProtectEncryptionAlgorithm("des-cbc"));
  size_t required = 0;
  for (const ProtectEncryptionAlgorithm& row : rows) {
    if (row.required) ++required;
  }
  EXPECT_EQ(required, 1U);
}

TEST(ProtectKeyMethodDescription, EachRowIsAnsweredFromItsOwnRequiredColumn) {
  for (const ProtectEncryptionAlgorithm& row : ProtectEncryptionAlgorithms()) {
    EXPECT_EQ(IsRequiredProtectEncryptionAlgorithm(row.identifier),
              row.required)
        << row.identifier;
  }
}

TEST(ProtectKeyMethodDescription,
     AnIdentifierOutsideTheTableIsRequiredOfNobody) {
  EXPECT_FALSE(
      IsRequiredProtectEncryptionAlgorithm("a-cipher-nobody-tabulated"));
  EXPECT_FALSE(IsRequiredProtectEncryptionAlgorithm("DES-CBC"));
}

TEST(ProtectKeyMethodDescription, EachRowNamesThePublishedAlgorithm) {
  std::span<const ProtectEncryptionAlgorithm> rows =
      ProtectEncryptionAlgorithms();
  ASSERT_EQ(rows.size(), 16U);
  EXPECT_NE(rows[0].algorithm.find("FIPS 46-3"), std::string_view::npos);
  EXPECT_NE(rows[2].algorithm.find("FIPS 197"), std::string_view::npos);
  EXPECT_NE(rows[12].algorithm.find("IETF RFC 2144"), std::string_view::npos);
  EXPECT_NE(rows[13].algorithm.find("IETF RFC 2437"), std::string_view::npos);
  EXPECT_NE(rows[15].algorithm.find("IETF RFC 2440"), std::string_view::npos);
}

TEST(ProtectKeyMethodDescription,
     AnIdentifierOutsideTheTableIsLeftToTheImplementation) {
  EXPECT_FALSE(IsProtectKeyMethodIdentifier("a-cipher-nobody-tabulated"));
  EXPECT_FALSE(IsProtectKeyMethodIdentifier("DES-CBC"));
  EXPECT_FALSE(IsProtectKeyMethodIdentifier(""));
}

TEST(ProtectKeyMethodDescription, TheIdentifiersAreTheOnesTheOtherCiphersUse) {
  for (const ProtectEncryptionAlgorithm& row : ProtectEncryptionAlgorithms()) {
    EXPECT_TRUE(IsProtectKeyMethodIdentifier(row.identifier)) << row.identifier;
    EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier(row.identifier))
        << row.identifier;
  }
  EXPECT_EQ(IsProtectKeyMethodIdentifier("a-cipher-nobody-tabulated"),
            IsProtectDigestKeyMethodIdentifier("a-cipher-nobody-tabulated"));
}

TEST(ProtectKeyMethodDescription,
     TheAlgorithmStandsUnchangedOnASignedEnvelope) {
  std::string envelope =
      SignedEnvelope(Writes("key_method", kProvidedCipher) +
                     Writes("digest_method", kDigestAlgorithm));
  EXPECT_EQ(IdentifierStatedFor(envelope, "key_method"), kProvidedCipher)
      << envelope;
  EXPECT_FALSE(Holds(envelope, "digest_method")) << envelope;
}

TEST(ProtectKeyMethodDescription,
     ASignedEnvelopeStatesTheCipherItsKeyBlocksAreUnder) {
  std::string envelope = SignedEnvelope("");
  EXPECT_EQ(IdentifierStatedFor(envelope, "key_method"), kProvidedCipher)
      << envelope;
}

TEST(ProtectKeyMethodDescription, TheAlgorithmStandsAheadOfTheBlocksItGoverns) {
  std::string envelope = SignedEnvelope("");
  size_t stated = envelope.find(kKeyMethodDirective);
  size_t block = envelope.find(kKeyBlockLine);
  ASSERT_NE(stated, std::string::npos) << envelope;
  ASSERT_NE(block, std::string::npos) << envelope;
  EXPECT_LT(stated, block) << envelope;
}

TEST(ProtectKeyMethodDescription, AnEnvelopeStatingOneIsReadBackAllTheSame) {
  EXPECT_TRUE(
      Holds(ReadBack(SignedEnvelope(Writes("key_method", kProvidedCipher))),
            kSealedDesign));
}

TEST(ProtectKeyMethodDescription, AnEnvelopeStatingNoneIsReadBackToo) {
  EXPECT_TRUE(Holds(ReadBack(SignedEnvelope("")), kSealedDesign));
}

TEST(ProtectKeyMethodEncryptionInput,
     ARegionAskingForTheRequiredCipherForItsKeysIsSealedUnderIt) {
  AuthorsRun run(SignedRegion(Writes("key_method", kKeyCipher)),
                 TheEntitysKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_EQ(IdentifierStatedFor(run.envelope, "key_method"), kKeyCipher)
      << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kSealedDesign)) << run.envelope;
}

TEST(ProtectKeyMethodEncryptionInput,
     AKeyBlockSealedUnderTheRequiredCipherIsOpenedUnderIt) {
  AuthorsRun run(SignedRegion(Writes("key_method", kKeyCipher)),
                 TheEntitysKey());
  EXPECT_TRUE(Holds(ReadBack(run.envelope), kSealedDesign)) << run.envelope;
}

TEST(ProtectKeyMethodEncryptionInput,
     ARegionAskingForAnOptionalCipherForItsKeysIsToldTheTableDoesNotRequireIt) {
  std::string source = "module bulkhead_m;\n";
  source.append(SignedRegion(Writes("key_method", kOptionalCipher)));
  source.append("endmodule\n");
  AuthorsRun run(source, TheEntitysKey());
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            AskingFor(kOptionalCipher, kTableLeavesItOptional),
                            6, "34.5.24.2"))
      << run.envelope;
}

TEST(ProtectKeyMethodEncryptionInput,
     ARegionAskingForTheCipherOurKeyBlocksUseDrawsNoReport) {
  AuthorsRun run(SignedRegion(Writes("key_method", kProvidedCipher)),
                 TheEntitysKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_EQ(IdentifierStatedFor(run.envelope, "key_method"), kProvidedCipher)
      << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kSealedDesign)) << run.envelope;
}

TEST(ProtectKeyMethodEncryptionInput,
     ARegionWhoseKeysTravelInNoBlockStatesNoCipherForThem) {
  AuthorsRun run(DirectRegion(Writes("key_method", kUnblockedCipher)),
                 TheDirectEntitysKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_EQ(TimesWritten(run.envelope, kKeyBlockLine), 0U) << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kKeyMethodDirective)) << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kSealedDesign)) << run.envelope;
}

}  // namespace
