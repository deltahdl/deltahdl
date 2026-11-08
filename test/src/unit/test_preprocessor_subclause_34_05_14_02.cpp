#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kProvider = "cerulean-vault";
constexpr std::string_view kBlockKeyName = "wrapping-2026";
constexpr std::string_view kBlockKey = "cerulean-vault-wrapping-key";

constexpr std::string_view kDataKeyName = "data-2026";

constexpr std::string_view kOtherProvider = "someone-else";
constexpr std::string_view kOtherKeyName = "theirs-2026";
constexpr std::string_view kOtherKey = "someone-elses-key";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string RegionUnderAKeyBlock() {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kProvider));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(Writes("key_keyname", kBlockKeyName));
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

ProtectKeyList TheBlockKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kProvider, kBlockKeyName, kBlockKey));
  return keys;
}

ProtectKeyList SomeoneElsesKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kOtherProvider, kOtherKeyName, kOtherKey));
  return keys;
}

std::string EnvelopeWithAKeyBlock() {
  std::string envelope =
      EncryptEnvelopes(RegionUnderAKeyBlock(), {}, TheBlockKey());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  return envelope;
}

uint32_t TheWrappedBlocksLine(std::string_view envelope) {
  return LineHolding(envelope, "`pragma protect data_block\n") + 1;
}

TEST(ProtectDataDecryptKeyDescription, TheKeyIsNotWrittenInTheClear) {
  std::string envelope = EnvelopeWithAKeyBlock();
  EXPECT_EQ(envelope.find("`pragma protect data_decrypt_key"),
            std::string::npos)
      << envelope;
}

TEST(ProtectDataDecryptKeyDescription, TheKeyInsideTheBlockOpensTheData) {
  PreprocFixture f;
  PreprocConfig config;
  config.protect_keys = TheBlockKey();
  std::string read = Preprocess(EnvelopeWithAKeyBlock(), f, config);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

TEST(ProtectDataDecryptKeyDescription, WithoutTheBlocksKeyTheDataStaysShut) {
  std::string envelope = EnvelopeWithAKeyBlock();
  PreprocFixture f;
  PreprocConfig config;
  config.protect_keys = SomeoneElsesKey();
  std::string read = Preprocess(envelope, f, config);
  EXPECT_EQ(read.find(kSealedDesign), std::string::npos) << read;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheWrappedBlocksLine(envelope), "34.3.2"))
      << read;
}

TEST(ProtectDataDecryptKeyDescription,
     TheNameInsideTheBlockNeedsNoKeyOfItsOwn) {
  std::string region = "`pragma protect begin\n";
  region.append(Writes("data_keyowner", kProvider));
  region.append(Writes("data_keyname", kDataKeyName));
  region.append(Writes("key_keyowner", kProvider));
  region.append(Writes("key_keyname", kBlockKeyName));
  region.append(kSealedDesign);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheBlockKey());
  ASSERT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  PreprocFixture f;
  PreprocConfig config;
  config.protect_keys = TheBlockKey();
  std::string read = Preprocess(envelope, f, config);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

std::string LineBeneath(std::string_view envelope, std::string_view keyword,
                        size_t from = 0) {
  std::string opening = "`pragma protect ";
  opening.append(keyword).append("\n");
  size_t at = envelope.find(opening, from);
  if (at == std::string_view::npos) return {};
  size_t starts = at + opening.size();
  return std::string(
      envelope.substr(starts, envelope.find('\n', starts) - starts));
}

TEST(ProtectDataDecryptKeyDescription, AKeyTheAuthorMadeSealsTheData) {
  constexpr std::string_view kAuthorsKey = "the-authors-own-data-key";
  std::string region = "`pragma protect begin\n";
  region.append(Writes("key_keyowner", kProvider));
  region.append(Writes("key_keyname", kBlockKeyName));
  region.append("`pragma protect data_decrypt_key\n");
  region.append(EncodeProtectValue(kAuthorsKey, DefaultProtectEncoding()));
  region.append("\n").append(kSealedDesign).append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheBlockKey());
  ASSERT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  std::string recovered;
  ASSERT_TRUE(DecryptProtectedRegion(LineBeneath(envelope, "data_block"),
                                     kAuthorsKey, &recovered))
      << envelope;
  EXPECT_NE(recovered.find(kSealedDesign), std::string::npos) << recovered;
  EXPECT_EQ(recovered.find("data_decrypt_key"), std::string::npos) << recovered;
}

TEST(ProtectDataDecryptKeyDescription, ALineTheSchemeNeverWroteIsNoKey) {
  std::string region = "`pragma protect begin\n";
  region.append(Writes("key_keyowner", kProvider));
  region.append(Writes("key_keyname", kBlockKeyName));
  region.append("`pragma protect data_decrypt_key\nnot a key!\n");
  region.append(kSealedDesign).append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheBlockKey());
  ASSERT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  std::string recovered;
  EXPECT_FALSE(DecryptProtectedRegion(LineBeneath(envelope, "data_block"),
                                      "not a key!", &recovered))
      << envelope;
}

}  // namespace
