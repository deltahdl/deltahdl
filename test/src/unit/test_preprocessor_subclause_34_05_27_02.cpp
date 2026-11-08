#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_protect_block_lines.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kFirstEntity = "meridian-trust";
constexpr std::string_view kSecondEntity = "cerulean-vault";
constexpr std::string_view kFirstKeyName = "wrapping-2026";
constexpr std::string_view kSecondKeyName = "wrapping-2027";
constexpr std::string_view kFirstKey = "meridian-trust-wrapping-key";
constexpr std::string_view kSecondKey = "cerulean-vault-wrapping-key";

constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kEncodingSealedDesign =
    "module sealed_m; endmodule\n";
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Designates(std::string_view entity, std::string_view key_name) {
  std::string text = Writes("key_keyowner", entity);
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(Writes("key_keyname", key_name));
  return text;
}

ProtectKeyList KeysOfBothEntities() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstEntity, kFirstKeyName, kFirstKey));
  keys.Add(KeyOf(kSecondEntity, kSecondKeyName, kSecondKey));
  return keys;
}

ProtectKeyList OnlyTheFirstEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstEntity, kFirstKeyName, kFirstKey));
  return keys;
}

ProtectKeyList OnlyTheSecondEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kSecondEntity, kSecondKeyName, kSecondKey));
  return keys;
}

std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kEncodingSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

std::string EnvelopeWithTwoBlocks() {
  std::string envelope =
      EncryptEnvelopes(Region(Designates(kFirstEntity, kFirstKeyName) +
                              Designates(kSecondEntity, kSecondKeyName)),
                       {}, KeysOfBothEntities());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 2U) << envelope;
  return envelope;
}

std::string EnvelopeWithOneBlock() {
  std::string envelope =
      EncryptEnvelopes(Region(Designates(kFirstEntity, kFirstKeyName)), {},
                       OnlyTheFirstEntitysKey());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  return envelope;
}

std::string BlockLineOf(const std::string& envelope) {
  size_t at = envelope.find(kKeyBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  size_t from = at + kKeyBlockLine.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

std::string RecoveredBufferOf(const std::string& envelope,
                              std::string_view key) {
  std::string block;
  EXPECT_TRUE(DecodeProtectBlock(BlockLineOf(envelope),
                                 DefaultProtectEncoding().enctype, &block))
      << envelope;
  std::string buffer;
  EXPECT_TRUE(DecryptProtectedBlock(block, key, &buffer)) << envelope;
  return buffer;
}

TEST(ProtectKeyBlockDescription, TheBufferCarriesWhatOpensTheDataBlock) {
  std::string buffer = RecoveredBufferOf(EnvelopeWithOneBlock(), kFirstKey);
  EXPECT_TRUE(Holds(buffer, "`pragma protect data_method=")) << buffer;
  EXPECT_TRUE(Holds(buffer, "`pragma protect data_decrypt_key\n")) << buffer;
}

TEST(ProtectKeyBlockDescription, TheDataNameIsInsideAndTheBlocksEntityOutside) {
  std::string envelope = EnvelopeWithOneBlock();
  std::string buffer = RecoveredBufferOf(envelope, kFirstKey);
  EXPECT_TRUE(Holds(buffer, Writes("data_keyname", kDataKeyName))) << buffer;
  EXPECT_FALSE(Holds(buffer, "key_keyowner")) << buffer;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyowner", kFirstEntity)))
      << envelope;
}

TEST(ProtectKeyBlockDescription, TheBlockIsTheBufferAndNothingAheadOfIt) {
  std::string buffer = RecoveredBufferOf(EnvelopeWithOneBlock(), kFirstKey);
  EXPECT_TRUE(buffer.rfind("`pragma protect data_method=", 0) == 0) << buffer;
}

TEST(ProtectKeyBlockDescription, AReaderOpeningEitherBlockReachesTheDesign) {
  std::string envelope = EnvelopeWithTwoBlocks();
  ReadSource first(envelope, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  ReadSource second(envelope,
                    ReadSource::KeysConfig(OnlyTheSecondEntitysKey()));
  EXPECT_TRUE(Holds(first.text, kEncodingSealedDesign)) << first.text;
  EXPECT_TRUE(Holds(second.text, kEncodingSealedDesign)) << second.text;
}

TEST(ProtectKeyBlockDescription, TwoBlocksAreWaysIntoOneEnvelope) {
  std::string envelope = EnvelopeWithTwoBlocks();
  ReadSource first(envelope, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  ReadSource second(envelope,
                    ReadSource::KeysConfig(OnlyTheSecondEntitysKey()));
  EXPECT_EQ(first.text, second.text);
  EXPECT_FALSE(first.diag.HasErrors()) << first.text;
  EXPECT_FALSE(second.diag.HasErrors()) << second.text;
}

TEST(ProtectKeyBlockDescription, AReaderHoldingNeitherKeyOpensNeitherBlock) {
  ReadSource run(EnvelopeWithTwoBlocks(),
                 ReadSource::KeysConfig(ProtectKeyList()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 20,
      "34.3.2"));
}

TEST(ProtectKeyBlockDescription, TheBlockThisReaderCannotOpenCostsItNoReport) {
  ReadSource run(EnvelopeWithTwoBlocks(),
                 ReadSource::KeysConfig(OnlyTheSecondEntitysKey()));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(run.diag.Diagnostics().empty()) << run.text;
}

TEST(ProtectKeyBlockDescription, AKeyBlockStandingOnSeveralLinesIsReadWhole) {
  std::string envelope = EnvelopeWithOneBlock();
  std::string broken = WithBlockBrokenIntoLines(envelope, kKeyBlockLine, 3);
  ASSERT_NE(broken, envelope);

  ReadSource run(broken, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(run.diag.Diagnostics().empty()) << run.text;
}

TEST(ProtectKeyBlockDescription, TheRecoveredTextIsReadAsDirectivesNotDesign) {
  std::string envelope = EnvelopeWithOneBlock();
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_FALSE(Holds(run.text, "`pragma protect data_decrypt_key")) << run.text;
  EXPECT_FALSE(Holds(run.text, BlockLineOf(envelope))) << run.text;
}

}  // namespace
