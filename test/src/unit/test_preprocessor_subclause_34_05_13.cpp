#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kKeyOwner = "acme";

constexpr std::string_view kOtherOwner = "globex";

constexpr std::string_view kPublicKey = "acme-rsa-public-key";

constexpr std::string_view kRegionKey = "acme-region-exchange-key";

constexpr std::string_view kKeyName = "acme-2026";

constexpr std::string_view kSecondKey = "acme-some-other-key-entirely";

constexpr std::string_view kUnavailableEnctype = "x-no-such-scheme-here";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

ProtectEncoding BlockEncoding() { return DefaultProtectEncoding(); }

ProtectEncoding Base64Encoding() {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBase64Enctype);
  return encoding;
}

ProtectKeyList KeyHeldUnder(std::string_view owner,
                            std::string_view designation,
                            std::string_view key = kRegionKey) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(designation), std::string(key)});
  return keys;
}

ProtectKeyList KeysUnderBothDesignations(std::string_view under_name,
                                         std::string_view under_public) {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(under_name)});
  keys.Add({std::string(kKeyOwner), std::string(kPublicKey),
            std::string(under_public)});
  return keys;
}

ProtectKeyList KeysUnderTwoEntities() {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(kRegionKey)});
  keys.Add({std::string(kKeyOwner), std::string(kPublicKey),
            std::string(kSecondKey)});
  keys.Add({std::string(kOtherOwner), std::string(kKeyName),
            std::string(kRegionKey)});
  keys.Add({std::string(kOtherOwner), std::string(kPublicKey),
            std::string(kRegionKey)});
  return keys;
}

std::string NamesKeyOwner(std::string_view owner) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  return text;
}

std::string NamesKeyName(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

std::string StatesEncoding(std::string_view enctype) {
  std::string text = "`pragma protect encoding=(enctype=\"";
  text.append(enctype).append("\")\n");
  return text;
}

std::string PublicKeyDesignation(std::string_view key,
                                 const ProtectEncoding& encoding) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(key, encoding)).append("\n");
  return text;
}

std::string Region(const std::string& described, std::string_view body) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(body);
  text.append("`pragma protect end\n");
  return text;
}

std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string Encrypted(const std::string& src, const ProtectKeyList& keys) {
  return EncryptEnvelopes(src, "", keys);
}

std::string EncryptedUnderOneKey(const std::string& src, std::string_view key) {
  return EncryptEnvelopes(src, key);
}

std::string EnvelopeFor(const std::string& described,
                        const ProtectKeyList& keys) {
  std::string envelope = Encrypted(Region(described, kSealedDesign), keys);
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos);
  return envelope;
}

std::string EnvelopeUnderOneKey(const std::string& described,
                                std::string_view key) {
  std::string envelope =
      EncryptedUnderOneKey(Region(described, kSealedDesign), key);
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos);
  return envelope;
}

struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ReadUnderKeys(const std::string& src, std::string_view key) {
    PreprocConfig config;
    config.protect_key = key;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

uint32_t TheDesignatedBlocksLine(std::string_view envelope) {
  return LineHolding(envelope, "`pragma protect data_block\n") + 1;
}

size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + 1);
  }
  return count;
}

TEST(ProtectDataPublicKeyEncryptionInput, TheLineBeneathTheKeywordPicksTheKey) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionInput,
     ALineTheSchemeNeverWroteDesignatesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += "`pragma protect data_public_key\n!! not an encoded value !!\n";
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionInput,
     TheKeywordCarryingAValueAnnouncesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += "`pragma protect data_public_key=\"against-the-keyword\"\n";
  described += EncodeProtectBlock(kPublicKey, BlockEncoding());
  described += "\n";
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionInput,
     ADesignationAheadOfTheRegionSelectsItsKey) {
  std::string src = NamesKeyOwner(kKeyOwner);
  src += PublicKeyDesignation(kPublicKey, BlockEncoding());
  src += Region(std::string(), kSealedDesign);
  std::string encrypted = Encrypted(src, KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionInput,
     TheStatedSchemeIsWhatTheLineIsReadUnder) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += StatesEncoding(kBase64Enctype);
  described += PublicKeyDesignation(kPublicKey, Base64Encoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionInput,
     TheSameCharactersUnderAnotherSchemeDesignateNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, Base64Encoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionInput,
     ASchemeThisToolHasNoneOfDesignatesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += StatesEncoding(kUnavailableEnctype);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionOutput,
     TheDesignationIsWrittenIntoTheBlockItWasUsedFor) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_EQ(Occurrences(encrypted, written), 1U);
  EXPECT_LT(encrypted.find("`pragma protect begin_protected"),
            encrypted.find(written));
  EXPECT_LT(encrypted.find(written),
            encrypted.find("`pragma protect end_protected"));
}

TEST(ProtectDataPublicKeyEncryptionOutput,
     ARegionDesignatingByNameWritesNoPublicKey) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kKeyName));
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect data_public_key"),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionOutput,
     TheValueIsWrittenInTheEnvelopesOwnScheme) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  described += StatesEncoding(kBase64Enctype);
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(PublicKeyDesignation(kPublicKey, Base64Encoding())),
            std::string::npos);
  EXPECT_EQ(encrypted.find(PublicKeyDesignation(kPublicKey, BlockEncoding())),
            std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionOutput,
     EachBlockTheDesignationWasUsedForCarriesIt) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string src = Region(described, "module first_m; endmodule\n");
  src += Region(described, "module second_m; endmodule\n");
  std::string encrypted = Encrypted(src, KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_EQ(Occurrences(encrypted, "`pragma protect begin_protected"), 2U);
  EXPECT_EQ(Occurrences(encrypted, written), 2U);
  EXPECT_EQ(encrypted.find("module first_m"), std::string::npos);
  EXPECT_EQ(encrypted.find("module second_m"), std::string::npos);
}

TEST(ProtectDataPublicKeyEncryptionOutput,
     ADesignationMadeAheadOfTheRegionIsWrittenIntoItsBlock) {
  std::string src = NamesKeyOwner(kKeyOwner);
  src += PublicKeyDesignation(kPublicKey, BlockEncoding());
  src += Region(std::string(), kSealedDesign);
  std::string encrypted = Encrypted(src, KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_EQ(Occurrences(encrypted, written), 2U);
  EXPECT_LT(encrypted.find("`pragma protect begin_protected"),
            encrypted.rfind(written));
  EXPECT_LT(encrypted.rfind(written),
            encrypted.find("`pragma protect end_protected"));
}

TEST(ProtectDataPublicKeyEncryptionOutput,
     TheCipherIsStatedInTheBlockAheadOfTheDesignation) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string method = "`pragma protect data_method=\"";
  method.append(kDataMethod).append("\"\n");
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_NE(encrypted.find(method), std::string::npos);
  EXPECT_LT(encrypted.find("`pragma protect begin_protected"),
            encrypted.find(method));
  EXPECT_LT(encrypted.find(method), encrypted.find(written));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheEntityAndThePublicKeyOpenTheBlock) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectDataPublicKeyDecryptionInput,
     ThePublicKeyIsReadAgainstTheEntityBesideIt) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string envelope =
      EnvelopeFor(described, KeyHeldUnder(kKeyOwner, kPublicKey));
  ReadUnderKeys read(envelope, KeyHeldUnder(kOtherOwner, kPublicKey));
  EXPECT_FALSE(read.Holds("module sealed_m"));
  EXPECT_TRUE(ReportedError(
      read.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheDesignatedBlocksLine(envelope), "34.3.2"));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheAnnouncedLineIsNotEmittedAsDesign) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_FALSE(read.Holds(EncodeProtectBlock(kPublicKey, BlockEncoding())));
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     AnEnvelopeDeclaringAnotherSchemeIsReadBackUnderIt) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += StatesEncoding(kBase64Enctype);
  described += PublicKeyDesignation(kPublicKey, Base64Encoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  std::string envelope = EnvelopeFor(described, keys);
  EXPECT_NE(envelope.find("enctype=\"base64\""), std::string::npos);
  ReadUnderKeys read(envelope, keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectDataPublicKeyDecryptionInput,
     AReaderHoldingOneKeyOpensTheBlockWithoutSelecting) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string envelope = EnvelopeUnderOneKey(described, kRegionKey);
  EXPECT_NE(envelope.find(PublicKeyDesignation(kPublicKey, BlockEncoding())),
            std::string::npos);
  ReadUnderKeys read(envelope, kRegionKey);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TwoDesignationsReachingOneKeyAreAccepted) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kRegionKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TwoDesignationsReachingTwoKeysAreReported) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kSecondKey);
  std::string envelope = EnvelopeFor(described, keys);
  ReadUnderKeys read(envelope, keys);
  EXPECT_TRUE(ReportedError(
      read.diag.Diagnostics(),
      "protect pragma data_public_key and data_keyname designate different "
      "keys of the data_keyowner in effect",
      LineHolding(envelope, "`pragma protect data_public_key") + 1, "34.5.13"));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TwoDesignationsReachingTwoKeysName34_5_13) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kSecondKey);
  std::string envelope = EnvelopeFor(described, keys);
  ReadUnderKeys read(envelope, keys);
  EXPECT_TRUE(ReportedError(
      read.diag.Diagnostics(),
      "protect pragma data_public_key and data_keyname designate different "
      "keys of the data_keyowner in effect",
      LineHolding(envelope, "`pragma protect data_public_key") + 1, "34.5.13"));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheDisagreementLeavesTheBlockReadable) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kSecondKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheEntityInEffectDecidesWhichKeysThePairIsReadAgainst) {
  std::string described = NamesKeyOwner(kOtherOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderTwoEntities();
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheNameWrittenAfterThePublicKeyCompletesThePair) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  described += NamesKeyName(kKeyName);
  std::string envelope = ForeignEnvelope(described);
  ReadUnderKeys read(envelope,
                     KeysUnderBothDesignations(kRegionKey, kSecondKey));
  EXPECT_TRUE(ReportedError(
      read.diag.Diagnostics(),
      "protect pragma data_public_key and data_keyname designate different "
      "keys of the data_keyowner in effect",
      LineHolding(envelope, "`pragma protect data_keyname"), "34.5.13"));
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheReversedOrderAcceptsAPairReachingOneKey) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  described += NamesKeyName(kKeyName);
  ReadUnderKeys read(ForeignEnvelope(described),
                     KeysUnderBothDesignations(kRegionKey, kRegionKey));
  EXPECT_EQ(read.diag.ErrorCount(), 0U);
}

TEST(ProtectDataPublicKeyDecryptionInput,
     OneDesignationReachingNothingDecidesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kKeyName);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheAlgorithmJoinsTheEntityAndTheDesignation) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  std::string envelope = EnvelopeFor(described, keys);

  const std::string kOurs = "`pragma protect data_method=\"x-deltahdl-stream\"";
  auto at = envelope.find(kOurs);
  ASSERT_NE(at, std::string::npos) << envelope;
  std::string theirs = "`pragma protect data_method=\"aes128-cbc\"";
  std::string retitled = envelope;
  retitled.replace(at, kOurs.size(), theirs);

  ReadUnderKeys read(retitled, keys);
  EXPECT_FALSE(read.Holds("module sealed_m")) << read.text;
  EXPECT_TRUE(ReportedError(
      read.diag.Diagnostics(),
      "states an encryption algorithm this implementation does not provide",
      TheDesignatedBlocksLine(retitled), "34.5.11.2"))
      << read.text;
}

TEST(ProtectDataPublicKeyDecryptionInput,
     TheSameEnvelopeOpensUnderTheAlgorithmItWasSealedWith) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m")) << read.text;
  EXPECT_FALSE(read.diag.HasErrors());
}

std::vector<Diagnostic> EncryptingReports(const ProtectKeyList& keys) {
  std::string src =
      Region(NamesKeyOwner(kKeyOwner) + NamesKeyName(kKeyName) +
                 PublicKeyDesignation(kPublicKey, DefaultProtectEncoding()),
             kSealedDesign);
  SourceManager mgr;
  DiagEngine diag(mgr);
  EncryptEnvelopes(src, "", keys, &diag, mgr.AddFile("<test>", src));
  return diag.Diagnostics();
}

constexpr std::string_view kTwoKeysDesignated =
    "protect pragma data_public_key and data_keyname designate different keys "
    "of the data_keyowner in effect";

TEST(ProtectDataPublicKeyEncryptionInput, TwoDesignationsOfTwoKeysAreReported) {
  EXPECT_TRUE(ReportedError(
      EncryptingReports(KeysUnderBothDesignations(kRegionKey, kSecondKey)),
      kTwoKeysDesignated, 1, "34.5.13"));
}

TEST(ProtectDataPublicKeyEncryptionInput, OneKeyOrAnUnheldOneIsNotReported) {
  EXPECT_FALSE(ReportedError(
      EncryptingReports(KeysUnderBothDesignations(kRegionKey, kRegionKey)),
      kTwoKeysDesignated, 1, "34.5.13"));
  EXPECT_FALSE(
      ReportedError(EncryptingReports(KeyHeldUnder(kKeyOwner, kKeyName)),
                    kTwoKeysDesignated, 1, "34.5.13"));
  EXPECT_FALSE(
      ReportedError(EncryptingReports(KeyHeldUnder(kKeyOwner, kPublicKey)),
                    kTwoKeysDesignated, 1, "34.5.13"));
}

}  // namespace
