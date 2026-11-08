#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

struct Recipient {
  std::string_view owner;
  std::string_view key_name;
  std::string_view key;
};
constexpr Recipient kVendor = {"orion-eda", "orion-2026",
                               "orion-recipient-key"};
constexpr Recipient kUser = {"vega-systems", "vega-2026", "vega-recipient-key"};

constexpr std::string_view kDesign = "  initial result = 42;\n";
constexpr std::string_view kSymmetricKeyName = "design-session-2026";

constexpr std::string_view kKeyBlockAnnouncement =
    "`pragma protect key_block\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

size_t Count(std::string_view text, std::string_view needle) {
  size_t count = 0;
  for (size_t pos = text.find(needle); pos != std::string_view::npos;
       pos = text.find(needle, pos + needle.size())) {
    ++count;
  }
  return count;
}

ProtectKeyList Keys(std::initializer_list<Recipient> recipients) {
  ProtectKeyList keys;
  for (const Recipient& r : recipients) {
    keys.Add(
        {std::string(r.owner), std::string(r.key_name), std::string(r.key)});
  }
  return keys;
}

std::string TheSendersInput() {
  std::string src = "`pragma protect begin\n";
  for (const Recipient& r : {kVendor, kUser}) {
    src += "`pragma protect key_keyowner=\"";
    src.append(r.owner).append("\"\n");
    src += "`pragma protect data_keyname=\"";
    src.append(kSymmetricKeyName).append("\"\n");
    src += "`pragma protect key_keyname=\"";
    src.append(r.key_name).append("\"\n");
  }
  src.append(kDesign);
  src += "`pragma protect end\n";
  return src;
}

std::string TheEnvelope() {
  return EncryptEnvelopes(TheSendersInput(), "", Keys({kVendor, kUser}));
}

std::string Produced(const std::string& envelope, const ProtectKeyList& keys) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = keys;
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

std::string FirstKeyBlockBuffer(const std::string& envelope,
                                std::string_view key) {
  size_t at = envelope.find(kKeyBlockAnnouncement);
  if (at == std::string::npos) return "";
  size_t from = at + kKeyBlockAnnouncement.size();
  std::string line = envelope.substr(from, envelope.find('\n', from) - from);
  std::string block;
  if (!DecodeProtectBlock(line, DefaultProtectEncoding().enctype, &block)) {
    return "";
  }
  std::string buffer;
  if (!DecryptProtectedBlock(block, key, &buffer)) return "";
  return buffer;
}

TEST(DigitalEnvelopes, TheMechanismIsAsTheAnnexDescribesIt) {
  EXPECT_TRUE(DigitalEnvelopeEncryptsTheDesignUnderASymmetricKey());
  EXPECT_TRUE(
      DigitalEnvelopeEncryptsTheSymmetricKeyUnderTheRecipientsPublicKey());
  EXPECT_EQ(KeywordRecordingTheEncryptedSymmetricKey(), "key_block");
  EXPECT_TRUE(
      IsProtectPragmaKeyword(KeywordRecordingTheEncryptedSymmetricKey()));
  EXPECT_TRUE(DigitalEnvelopesCanBeCreatedUnderEitherSecretKeyScheme());
  EXPECT_TRUE(AnEnvelopeWithSeveralKeyBlocksOpensToSeveralRecipients());
}

TEST(DigitalEnvelopes, EachRecipientOpensTheOneEnvelopeWithItsOwnKey) {
  std::string envelope = TheEnvelope();
  EXPECT_EQ(Count(envelope, kKeyBlockAnnouncement), 2u);
  EXPECT_FALSE(Holds(envelope, "result = 42"));
  EXPECT_TRUE(
      Holds(Produced(envelope, Keys({kVendor})), "initial result = 42;"));
  EXPECT_TRUE(Holds(Produced(envelope, Keys({kUser})), "initial result = 42;"));
  EXPECT_FALSE(Holds(Produced(envelope, ProtectKeyList()), "result = 42"));
}

TEST(DigitalEnvelopes,
     TheKeyBlockCarriesTheSymmetricKeyItselfAsTheAnnexPrefers) {
  EXPECT_EQ(DataKeySpecificationNeedingTheKeyAtTheDecryptingTool(),
            DataKeySpecification::kKeyownerAndKeyname);
  EXPECT_EQ(DataKeySpecificationTheAnnexPrefers(),
            DataKeySpecification::kDataDecryptKey);
  EXPECT_EQ(DataKeySpecificationThisToolWritesIntoAKeyBlock(),
            DataKeySpecificationTheAnnexPrefers());
  std::string envelope = TheEnvelope();
  EXPECT_FALSE(Holds(envelope, "data_decrypt_key"));
  std::string buffer = FirstKeyBlockBuffer(envelope, kVendor.key);
  EXPECT_TRUE(Holds(buffer, "`pragma protect data_method="));
  EXPECT_TRUE(Holds(buffer, "`pragma protect data_decrypt_key\n"));
  EXPECT_TRUE(FirstKeyBlockBuffer(envelope, kUser.key).empty());
}

}  // namespace
