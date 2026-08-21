// §34.5.27.2 key_block, Description, on what a block carries and who may open
// it.
//
// The subclause states four things. One is a condition on an encrypting tool's
// input -- a block found outside a previously generated envelope is an error,
// and inside one it is ignored -- and the file named for §34.5.27 covers that
// and says so. That file also covers the error a region draws by changing its
// data decryption pragma expressions between two of its blocks. The other two
// are what this file is for.
//
//   ENCRYPTION OUTPUT: the tool forms a buffer from the expressions that open
//   the region's data, encrypts it, encodes it under the encoding pragma
//   expression in effect, and writes the result as the block's contents. Where
//   several blocks stand in one envelope they are alternative decryption keys
//   for it rather than several envelopes.
//
//   DECRYPTION INPUT: the block is read in the encoded form, the encoding is
//   reversed, the block is decrypted, and the resulting text is parsed for the
//   keys the data block needs.
//
// The initialization vector never arises. §34.5.27.2 has the vector prepended
// to the encrypted key wherever the cipher a region's keys are under is a CBC
// algorithm requiring one, and the cipher this implementation has is a keyed
// stream named as its own rather than as one the standard reserves. There is
// nothing to prepend and nothing to strip, and a case below states it: the
// decoded block is the buffer and nothing standing ahead of it.
//
// Which spelling of the keyword announces the block is §34.5.27.1's and is
// stated in test_preprocessor_subclause_34_05_27_01.cpp.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// Two entities, each holding one key. A region designating both is written a
// block for each, and §34.5.27 makes those two alternative ways into one
// envelope rather than two envelopes.
constexpr std::string_view kFirstEntity = "meridian-trust";
constexpr std::string_view kSecondEntity = "cerulean-vault";
constexpr std::string_view kFirstKeyName = "wrapping-2026";
constexpr std::string_view kSecondKeyName = "wrapping-2027";
constexpr std::string_view kFirstKey = "meridian-trust-wrapping-key";
constexpr std::string_view kSecondKey = "cerulean-vault-wrapping-key";

// The name a region gives the key its data are under. A name with no key held
// for it is what sends the region to key blocks rather than to a key of its
// author's.
constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// One designation of a key block's key: the entity, the name of the key the
// data are under, and the name picking the block's own key out of that entity's
// list. The data name is written with each designation because §34.5.27 holds
// the blocks of one envelope to agreeing about the data.
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

// A region designating `described`, sealing the design behind key blocks.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The envelope this tool writes for a region designating both entities,
// checked on the way out to be one carrying a block for each.
std::string EnvelopeWithTwoBlocks() {
  std::string envelope =
      EncryptEnvelopes(Region(Designates(kFirstEntity, kFirstKeyName) +
                              Designates(kSecondEntity, kSecondKeyName)),
                       {}, KeysOfBothEntities());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 2U) << envelope;
  return envelope;
}

// The envelope for a region designating one entity.
std::string EnvelopeWithOneBlock() {
  std::string envelope =
      EncryptEnvelopes(Region(Designates(kFirstEntity, kFirstKeyName)), {},
                       OnlyTheFirstEntitysKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockLine), 1U) << envelope;
  return envelope;
}

// The characters the first key block of `envelope` was written as, which is
// the line beneath the keyword announcing it.
std::string BlockLineOf(const std::string& envelope) {
  size_t at = envelope.find(kKeyBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  size_t from = at + kKeyBlockLine.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

// That block read the way §34.5.27.2 has a reader read it: out of the coding
// scheme it was written in, then out of the key it was encrypted under.
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

// -- What the block carries --------------------------------------------------

// §34.5.27.2: the buffer is formed from the expressions that open the region's
// data. What a reader is here for is the key, and the cipher it belongs to
// stands beside it: neither opens the data block without the other.
TEST(ProtectKeyBlockDescription, TheBufferCarriesWhatOpensTheDataBlock) {
  std::string buffer = RecoveredBufferOf(EnvelopeWithOneBlock(), kFirstKey);
  EXPECT_TRUE(Holds(buffer, "`pragma protect data_method=")) << buffer;
  EXPECT_TRUE(Holds(buffer, "`pragma protect data_decrypt_key\n")) << buffer;
}

// The subclause admits any of the expressions naming the data's key and this
// buffer carries two of them. The designations already stand in the clear
// beside the block, so a copy sealed inside would say nothing the envelope does
// not, and a reader would have opened the block to learn what it knew already.
TEST(ProtectKeyBlockDescription, TheDesignationsStayOutsideTheBlock) {
  std::string envelope = EnvelopeWithOneBlock();
  std::string buffer = RecoveredBufferOf(envelope, kFirstKey);
  EXPECT_FALSE(Holds(buffer, "data_keyname")) << buffer;
  EXPECT_FALSE(Holds(buffer, "key_keyowner")) << buffer;
  EXPECT_TRUE(Holds(envelope, Writes("data_keyname", kDataKeyName)))
      << envelope;
}

// §34.5.27.2 has the encrypted region encoded under the encoding pragma
// expression in effect, so the characters beneath the keyword are the buffer
// written in that scheme and nothing else: read out of the scheme and out of
// the key, what is left is the buffer whole.
//
// That is also where the initialization vector would have been. §34.5.27.2
// prepends one to the encrypted key wherever the cipher is a CBC algorithm
// requiring it, and the cipher here requires none, so nothing stands ahead of
// the buffer.
TEST(ProtectKeyBlockDescription, TheBlockIsTheBufferAndNothingAheadOfIt) {
  std::string buffer = RecoveredBufferOf(EnvelopeWithOneBlock(), kFirstKey);
  EXPECT_TRUE(buffer.rfind("`pragma protect data_method=", 0) == 0) << buffer;
}

// -- Alternative ways into one envelope --------------------------------------

// §34.5.27.2: several blocks in one envelope are alternative decryption keys
// for it rather than several envelopes. A reader holding either entity's key
// opens the block written for it and reaches the same design.
TEST(ProtectKeyBlockDescription, AReaderOpeningEitherBlockReachesTheDesign) {
  std::string envelope = EnvelopeWithTwoBlocks();
  ReadSource first(envelope, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  ReadSource second(envelope,
                    ReadSource::KeysConfig(OnlyTheSecondEntitysKey()));
  EXPECT_TRUE(Holds(first.text, kSealedDesign)) << first.text;
  EXPECT_TRUE(Holds(second.text, kSealedDesign)) << second.text;
}

// The two blocks encode the same data decryption key data, which is what makes
// them ways into one envelope rather than two: the design each reader reaches
// is the same design, and the block the other reader could not open cost
// neither of them anything.
TEST(ProtectKeyBlockDescription, TwoBlocksAreWaysIntoOneEnvelope) {
  std::string envelope = EnvelopeWithTwoBlocks();
  ReadSource first(envelope, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  ReadSource second(envelope,
                    ReadSource::KeysConfig(OnlyTheSecondEntitysKey()));
  EXPECT_EQ(first.text, second.text);
  EXPECT_FALSE(first.diag.HasErrors()) << first.text;
  EXPECT_FALSE(second.diag.HasErrors()) << second.text;
}

// A reader holding neither entity's key opens neither block, and §34.5.27 has
// that cost nothing to say: a block written for somebody else is not a breach.
// What the reading is left without is the design.
TEST(ProtectKeyBlockDescription, AReaderHoldingNeitherKeyOpensNeitherBlock) {
  ReadSource run(EnvelopeWithTwoBlocks(),
                 ReadSource::KeysConfig(ProtectKeyList()));
  EXPECT_FALSE(Holds(run.text, kSealedDesign)) << run.text;
}

// -- What the recovered text is read as --------------------------------------

// §34.5.27.2: the resulting text is parsed to determine the keys the data block
// needs. What it recovers to is protect pragma directives, so the reading is
// the one every directive of the source goes through, and what it puts in
// effect is what the data block is then opened with.
//
// The block's own text is not text of the design: it holds keys rather than
// lines, so none of it comes back out.
TEST(ProtectKeyBlockDescription, TheRecoveredTextIsReadAsDirectivesNotDesign) {
  std::string envelope = EnvelopeWithOneBlock();
  ReadSource run(envelope, ReadSource::KeysConfig(OnlyTheFirstEntitysKey()));
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
  EXPECT_FALSE(Holds(run.text, "`pragma protect data_decrypt_key")) << run.text;
  EXPECT_FALSE(Holds(run.text, BlockLineOf(envelope))) << run.text;
}

}  // namespace
