#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The recipient: its owner identity, the name of the key of its that the
// sender holds, and the key.
constexpr std::string_view kRecipient = "cygnus-eda";
constexpr std::string_view kRecipientsKeyName = "cygnus-2026";
constexpr std::string_view kRecipientsKey = "cygnus-envelope-key";

// The owner and name of the symmetric key the design is under, which no run
// holds and the sender's run therefore makes.
constexpr std::string_view kProvider = "halo-ip";
constexpr std::string_view kProvidersKeyName = "halo-2026";

// The design, and the licences written beside it inside the block.
constexpr std::string_view kDesign = "  initial result = 42;\n";
constexpr std::string_view kDecryptLicense =
    "`pragma protect decrypt_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"open\")\n";
constexpr std::string_view kRuntimeLicense =
    "`pragma protect runtime_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"run\")\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// The keys the sender's run and the recipient's run hold.
ProtectKeyList RecipientsKeys() {
  ProtectKeyList keys;
  keys.Add({std::string(kRecipient), std::string(kRecipientsKeyName),
            std::string(kRecipientsKey)});
  return keys;
}

// An input of §O.5.1 with cleartext on either side of its one block: the
// recipient's key designated ahead of the block with the author's name and
// information, the data key's owner and name, and a digest asked for, and
// the licences and the design inside it.
std::string TheSendersInput() {
  std::string src = "module m;\n";
  src += "`pragma protect author=\"Halo Author\"\n";
  src += "`pragma protect author_info=\"revision 7\"\n";
  src += "`pragma protect key_keyowner=\"";
  src.append(kRecipient).append("\"\n");
  src += "`pragma protect key_keyname=\"";
  src.append(kRecipientsKeyName).append("\"\n");
  src += "`pragma protect data_keyowner=\"";
  src.append(kProvider).append("\"\n");
  src += "`pragma protect data_keyname=\"";
  src.append(kProvidersKeyName).append("\"\n");
  src += "`pragma protect digest_block\n";
  src += "`pragma protect begin\n";
  src.append(kDecryptLicense).append(kRuntimeLicense).append(kDesign);
  src += "`pragma protect end\n";
  src += "endmodule\n";
  return src;
}

// The envelope the sender's run writes for that input.
std::string TheEnvelope() {
  return EncryptEnvelopes(TheSendersInput(), "", RecipientsKeys());
}

// The line on which `envelope` records `block` beneath its keyword.
std::string BlockBeneath(std::string_view envelope, std::string_view block) {
  std::string keyword = "`pragma protect ";
  keyword.append(block).append("\n");
  size_t at = envelope.find(keyword);
  if (at == std::string_view::npos) return "";
  size_t from = at + keyword.size();
  return std::string(envelope.substr(from, envelope.find('\n', from) - from));
}

// The text the recipient's run, holding its own key, produces from
// `envelope`.
std::string TheRecipientGets(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = RecipientsKeys();
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<recipient>", envelope));
}

// §O.5.2: the output is the cleartext copied to its sections and, for each
// block, the eleven expressions, the key block holding the data key's owner,
// the data_method and the data key itself, the data composed of the
// licences and the text, and the blocks on the lines beneath their keywords.
TEST(DigitalEnvelopeOutput, TheOutputIsWhatTheAnnexHasTheToolGenerate) {
  EXPECT_TRUE(CleartextIsCopiedToTheDigitalEnvelopeOutput());
  auto expressions = ExpressionsTheDigitalEnvelopeOutputCarries();
  ASSERT_EQ(expressions.size(), 11u);
  EXPECT_EQ(expressions[0], "begin_protected");
  EXPECT_EQ(expressions[1], "key_keyowner");
  EXPECT_EQ(expressions[2], "key_method");
  EXPECT_EQ(expressions[3], "key_keyname");
  EXPECT_EQ(expressions[4], "key_block");
  EXPECT_EQ(expressions[5], "encoding");
  EXPECT_EQ(expressions[6], "author");
  EXPECT_EQ(expressions[7], "author_info");
  EXPECT_EQ(expressions[8], "digest_block");
  EXPECT_EQ(expressions[9], "data_block");
  EXPECT_EQ(expressions[10], "end_protected");
  for (std::string_view name : expressions) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
  }
  auto contents = WhatTheDigitalEnvelopeKeyBlockContains();
  ASSERT_EQ(contents.size(), 3u);
  EXPECT_EQ(contents[0], "data_keyowner");
  EXPECT_EQ(contents[1], "data_method");
  EXPECT_EQ(contents[2], "data_decrypt_key");
  auto composition = WhatTheDigitalEnvelopeDataBlockIsComposedOf();
  ASSERT_EQ(composition.size(), 3u);
  EXPECT_EQ(composition[0], "decrypt_license");
  EXPECT_EQ(composition[1], "runtime_license");
  EXPECT_TRUE(DigitalEnvelopeKeyBlockDataStandBeneathTheKeyword());
}

// §O.5.2 against the flow: the cleartext on either side of the block is in
// the output, and the block became a region carrying each of the eleven
// expressions, the author's name and information among them since the
// input provided them, with the digest and the data beneath their keywords.
TEST(DigitalEnvelopeOutput, TheCleartextIsCopiedAndTheExpressionsGenerated) {
  std::string envelope = TheEnvelope();
  EXPECT_TRUE(Holds(envelope, "module m;\n"));
  EXPECT_TRUE(Holds(envelope, "endmodule\n"));
  for (std::string_view name : ExpressionsTheDigitalEnvelopeOutputCarries()) {
    std::string expression = "`pragma protect ";
    expression.append(name);
    EXPECT_TRUE(Holds(envelope, expression)) << name << "\n" << envelope;
  }
  EXPECT_TRUE(Holds(envelope, "author=\"Halo Author\""));
  EXPECT_TRUE(Holds(envelope, "author_info=\"revision 7\""));
  EXPECT_FALSE(BlockBeneath(envelope, "key_block").empty());
  EXPECT_FALSE(BlockBeneath(envelope, "digest_block").empty());
  EXPECT_FALSE(BlockBeneath(envelope, "data_block").empty());
}

// §O.5.2 against the flow: the key block, opened under the recipient's key,
// holds the data key's owner, the data_method and the data key itself, none
// of which is in the clear; and the data block holds the licences and the
// text, none in the clear either, which the recipient's run gets back.
TEST(DigitalEnvelopeOutput, TheKeyBlockAndTheDataBlockHoldWhatTheAnnexSays) {
  std::string envelope = TheEnvelope();
  std::string key_block;
  ASSERT_TRUE(DecryptProtectedRegion(BlockBeneath(envelope, "key_block"),
                                     kRecipientsKey, &key_block))
      << envelope;
  EXPECT_TRUE(Holds(key_block, "`pragma protect data_keyowner=\"halo-ip\""));
  EXPECT_TRUE(Holds(key_block, "`pragma protect data_method="));
  EXPECT_TRUE(Holds(key_block, "`pragma protect data_decrypt_key\n"));
  EXPECT_FALSE(Holds(envelope, "data_decrypt_key"));
  EXPECT_FALSE(Holds(envelope, "feature=\"open\""));
  EXPECT_FALSE(Holds(envelope, "feature=\"run\""));
  EXPECT_FALSE(Holds(envelope, "result = 42"));
  EXPECT_TRUE(Holds(TheRecipientGets(envelope), "initial result = 42;"));
}

}  // namespace
