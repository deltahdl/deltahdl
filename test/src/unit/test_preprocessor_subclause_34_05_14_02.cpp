// §34.5.14.2 data_decrypt_key, Description.
//
// The subclause says three things about the keyword §34.5.14.1 spells.
//
//   Written in an encrypting tool's input, it says the next line holds the
//   encoded value of the key that will decrypt the data_block, and it should
//   only be used where digital signatures are. An author generates a key, seals
//   the cleartext with it, and stores that as the data_block; the data_method
//   and this key are then encrypted under the key_method and stored as the
//   contents of the key_block, the data_block itself not being re-encrypted.
//
//   In a tool's output the key is part of the encrypted content of the
//   key_block, encoded as the encoding pragma expression states.
//
//   On the way back, a tool that finds a digital signature was in use decrypts
//   the key_block to find the data_decrypt_key and the data_method, and those
//   in turn decrypt the data_block.
//
// The last two are what a run can be held to, and they are one claim seen from
// each side: the key that opens a region's data travels inside the region's key
// block rather than beside it. §34.5.27 covers what a key block is and when a
// region gets one; what is left here is that the key inside it is the one the
// data block is opened with, which is why a reading that cannot open the key
// block cannot open the data either.
//
// A region reaches that arrangement by designating a key for its key block and
// naming none for its data directly (§34.5.23 and §34.5.25 write the
// designation), which is the shape the cases below build.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity that provided the key a region's key block is under, the name
// picking that key out, and the key itself.
constexpr std::string_view kProvider = "cerulean-vault";
constexpr std::string_view kBlockKeyName = "wrapping-2026";
constexpr std::string_view kBlockKey = "cerulean-vault-wrapping-key";

// The name a region gives the key its data are under. It is designated but no
// key is held for it directly, which is what sends the region to a key block.
constexpr std::string_view kDataKeyName = "data-2026";

// A key of another entity, for the reading that holds keys and none of them the
// one the block is under. A reading holding nothing at all would fail for want
// of any key rather than for want of this one.
constexpr std::string_view kOtherProvider = "someone-else";
constexpr std::string_view kOtherKeyName = "theirs-2026";
constexpr std::string_view kOtherKey = "someone-elses-key";

// The design a region seals.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// A region designating the key its key block is under and naming the key its
// data are under, with the design between the delimiters of §34.5.1 and
// §34.5.2.
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

// The envelope this tool writes for that region, checked on the way out to be
// one that carries a key block: without it the cases below would be about a
// region sealed some other way.
std::string EnvelopeWithAKeyBlock() {
  std::string envelope =
      EncryptEnvelopes(RegionUnderAKeyBlock(), {}, TheBlockKey());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  return envelope;
}

// §34.5.14.2: the key is part of the encrypted content of the key block, so it
// does not stand in the envelope as a directive of its own. An envelope writing
// it in the clear would be handing out the key that opens its own data.
TEST(ProtectDataDecryptKeyDescription, TheKeyIsNotWrittenInTheClear) {
  std::string envelope = EnvelopeWithAKeyBlock();
  EXPECT_EQ(envelope.find("`pragma protect data_decrypt_key"),
            std::string::npos)
      << envelope;
}

// §34.5.14.2: a reading decrypts the key block to find the key, and that key
// decrypts the data block. Holding the key the block is under is what opens
// both, and the design comes back.
TEST(ProtectDataDecryptKeyDescription, TheKeyInsideTheBlockOpensTheData) {
  PreprocFixture f;
  PreprocConfig config;
  config.protect_keys = TheBlockKey();
  std::string read = Preprocess(EnvelopeWithAKeyBlock(), f, config);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

// The same envelope read by a tool holding a key of another entity and none of
// the one the block is under. The key block stays shut, so the data stays shut
// with it -- which is what makes the case above about the key inside the block
// rather than about a region that opens for anyone.
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
      LineHolding(envelope, "data_block"), "34.3.2"))
      << read;
}

}  // namespace
