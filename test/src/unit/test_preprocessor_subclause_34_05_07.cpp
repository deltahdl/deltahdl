#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kKeyOwner = "acme";
constexpr std::string_view kKeyName = "acme-2026";

constexpr std::string_view kRegionKey = "acme-region-exchange-key";

constexpr std::string_view kUnheldKeyName = "acme-key-nobody-supplied";

constexpr std::string_view kInputAgent = "AcmeCrypt";

constexpr std::string_view kOtherAgent = "Globex Sealer 7";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

constexpr std::string_view kBlockOpening = "`pragma protect data_block\n";

constexpr std::string_view kAgentDirectiveOpening =
    "`pragma protect encrypt_agent=";

ProtectKeyList KeysHeldUnder(std::string_view held_as) {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(held_as), std::string(kRegionKey)});
  return keys;
}

std::string NamesTheKey() {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kKeyOwner).append("\"\n`pragma protect data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

std::string NamesAgent(std::string_view name) {
  std::string text = "`pragma protect encrypt_agent=\"";
  text.append(name).append("\"\n");
  return text;
}

std::string NamesAgentInAList(std::string_view name) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kKeyOwner).append("\"\n`pragma protect encrypt_agent=\"");
  text.append(name).append("\", data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

std::string GeneratedAgentDirective() {
  std::string text = "`pragma protect encrypt_agent=\"";
  text.append(kEncryptAgent).append("\"\n");
  return text;
}

std::string Region(const std::string& described,
                   std::string_view design = kSealedDesign) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(design);
  text.append("`pragma protect end\n");
  return text;
}

std::string SealedModelNaming(std::string_view name) {
  std::string text(kBeginProtected);
  text.append(NamesAgent(name)).append(kEndProtected);
  return text;
}

std::string EncryptedUnder(const std::string& src, std::string_view held_as) {
  return EncryptEnvelopes(src, "", KeysHeldUnder(held_as));
}

std::string Encrypted(const std::string& src) {
  return EncryptedUnder(src, kKeyName);
}

std::string OpenedBlockOf(const std::string& envelope) {
  size_t at = envelope.find(kBlockOpening);
  if (at == std::string::npos) return {};
  size_t start = at + kBlockOpening.size();
  size_t end = envelope.find('\n', start);
  if (end == std::string::npos) return {};
  std::string cleartext;
  if (!DecryptProtectedRegion(envelope.substr(start, end - start), kRegionKey,
                              &cleartext)) {
    return {};
  }
  return cleartext;
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

struct ReadingUnderTheKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadingUnderTheKey(const std::string& src) {
    PreprocConfig config;
    config.protect_keys = KeysHeldUnder(kKeyName);
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

TEST(ProtectEncryptAgentEncryptionInput, TheToolWritesItsOwnNameOverTheInputs) {
  std::string described = NamesTheKey() + NamesAgent(kInputAgent);
  std::string encrypted = Encrypted(Region(described));
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 1U);
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_EQ(encrypted.find(NamesAgent(kInputAgent)), std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, AnExpressionInTheRegionIsSealed) {
  std::string described = NamesTheKey() + NamesAgent(kInputAgent);
  std::string opened = OpenedBlockOf(Encrypted(Region(described)));
  EXPECT_NE(opened.find(kSealedDesign), std::string::npos);
  EXPECT_NE(opened.find(NamesAgent(kInputAgent)), std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, TheStatedBlockSizeCountsTheLine) {
  std::string described = NamesTheKey() + NamesAgent(kInputAgent);
  std::string sealed = described + std::string(kSealedDesign);
  std::string bytes = "bytes=";
  bytes.append(std::to_string(ProtectedRegionBlockSize(sealed))).append(")");
  EXPECT_NE(Encrypted(Region(described)).find(bytes), std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, TheKeywordStandingAloneIsSealedToo) {
  std::string described = NamesTheKey() + "`pragma protect encrypt_agent\n";
  std::string encrypted = Encrypted(Region(described));
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 1U);
  EXPECT_NE(OpenedBlockOf(encrypted).find("`pragma protect encrypt_agent\n"),
            std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, AnIdentifierValueIsSealedToo) {
  std::string described =
      NamesTheKey() + "`pragma protect encrypt_agent=acme_crypt\n";
  std::string encrypted = Encrypted(Region(described));
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_NE(OpenedBlockOf(encrypted).find("encrypt_agent=acme_crypt"),
            std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, ANumberValueIsSealedToo) {
  std::string described =
      NamesTheKey() + "`pragma protect encrypt_agent=1998\n";
  std::string encrypted = Encrypted(Region(described));
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_NE(OpenedBlockOf(encrypted).find("encrypt_agent=1998"),
            std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, AnExpressionInAListIsPassedToo) {
  std::string encrypted = Encrypted(Region(NamesAgentInAList(kInputAgent)));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionInput, AnExpressionOutsideEnvelopesStays) {
  std::string src = "module m;\n";
  src.append("`pragma  protect   encrypt_agent  =  \"AcmeCrypt\"\n");
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectEncryptAgentEncryptionInput, AnExpressionAheadOfTheEnvelopeStays) {
  std::string encrypted =
      Encrypted(NamesAgent(kInputAgent) + Region(NamesTheKey()));
  EXPECT_EQ(Occurrences(encrypted, NamesAgent(kInputAgent)), 1U);
  EXPECT_LT(encrypted.find(NamesAgent(kInputAgent)),
            encrypted.find(kBeginProtected));
}

TEST(ProtectEncryptAgentEncryptionInput, ANameFromAnEarlierRegionIsNotUsed) {
  std::string first = Region(NamesTheKey() + NamesAgent(kInputAgent));
  std::string second = Region(NamesTheKey(), "module second_m; endmodule\n");
  std::string encrypted = Encrypted(first + second);
  EXPECT_EQ(Occurrences(encrypted, kBeginProtected), 2U);
  EXPECT_EQ(Occurrences(encrypted, GeneratedAgentDirective()), 2U);
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 2U);
}

TEST(ProtectEncryptAgentEncryptionOutput, TheToolGeneratesTheExpressionItself) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, GeneratedAgentDirective()), 1U);
}

TEST(ProtectEncryptAgentEncryptionOutput, AnEnvelopeIsDescribedByItsMaker) {
  std::string encrypted =
      Encrypted(NamesAgent(kInputAgent) + Region(NamesTheKey()));
  size_t envelope = encrypted.find(kBeginProtected);
  EXPECT_LT(envelope, encrypted.find(GeneratedAgentDirective()));
  EXPECT_EQ(encrypted.find(NamesAgent(kInputAgent), envelope),
            std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionOutput, TheStringAgainstTheKeywordNamesIt) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_FALSE(kEncryptAgent.empty());
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect encrypt_agent\n"),
            std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionOutput, TheDirectiveStandsInsideTheEnvelope) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_LT(encrypted.find(kBeginProtected),
            encrypted.find(GeneratedAgentDirective()));
  EXPECT_LT(encrypted.find(GeneratedAgentDirective()),
            encrypted.find(kEndProtected));
}

TEST(ProtectEncryptAgentEncryptionOutput, TheDirectiveStandsAheadOfTheBlock) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_NE(encrypted.find(kBlockOpening), std::string::npos);
  EXPECT_LT(encrypted.find(GeneratedAgentDirective()),
            encrypted.find(kBlockOpening));
}

TEST(ProtectEncryptAgentEncryptionOutput, ARegionWithNoKeyGetsNoExpression) {
  std::string src = Region(NamesTheKey() + NamesAgent(kInputAgent));
  EXPECT_EQ(EncryptedUnder(src, kUnheldKeyName), src);
}

TEST(ProtectEncryptAgentEncryptionOutput, TheBlockIsTheOneTheRegionsTextGives) {
  std::string described = NamesTheKey();
  std::string encrypted = Encrypted(Region(described));
  EXPECT_NE(encrypted.find(kBlockOpening), std::string::npos);
  EXPECT_EQ(OpenedBlockOf(encrypted), described + std::string(kSealedDesign));
}

TEST(ProtectEncryptAgentEncryptionOutput, ASealedModelsNameDisplacesNothing) {
  std::string described = NamesTheKey() + SealedModelNaming(kOtherAgent);
  std::string encrypted = Encrypted(Region(described));
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 1U);
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
}

TEST(ProtectEncryptAgentEncryptionOutput, ASealedModelsNameIsSealedWithIt) {
  std::string described = NamesTheKey() + SealedModelNaming(kOtherAgent);
  std::string opened = OpenedBlockOf(Encrypted(Region(described)));
  EXPECT_NE(opened.find(NamesAgent(kOtherAgent)), std::string::npos);
}

TEST(ProtectEncryptAgentDecryptionInput, TheNameReachesNoneOfTheDesignText) {
  ReadingUnderTheKey read(Encrypted(Region(NamesTheKey())));
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kEncryptAgent));
}

TEST(ProtectEncryptAgentDecryptionInput, TheNameCostsTheReadingNothing) {
  ReadingUnderTheKey read(Encrypted(Region(NamesTheKey())));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectEncryptAgentDecryptionInput, ASealedModelsNameReachesNoDesignText) {
  std::string described = NamesTheKey() + SealedModelNaming(kOtherAgent);
  ReadingUnderTheKey read(Encrypted(Region(described)));
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kOtherAgent));
}

TEST(ProtectEncryptAgentDecryptionInput, AForeignEnvelopeNamingAnAgentIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesAgent(kInputAgent)).append(kEndProtected);
  ReadingUnderTheKey read(envelope);
  EXPECT_FALSE(read.Holds(kInputAgent));
}

}  // namespace
