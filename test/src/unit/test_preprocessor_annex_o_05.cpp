#include <gtest/gtest.h>

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

// Two recipients of one envelope -- a tool vendor and a user -- each with a
// key of its own that the sender holds and that the recipient's decrypting
// run holds, standing for the public and the private key of the pair.
struct Recipient {
  std::string_view owner;
  std::string_view key_name;
  std::string_view key;
};
constexpr Recipient kVendor = {"orion-eda", "orion-2026",
                               "orion-recipient-key"};
constexpr Recipient kUser = {"vega-systems", "vega-2026", "vega-recipient-key"};

// The design the sender protects, under a symmetric key of its own name that
// no recipient holds.
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

// The sender's input: one region naming the symmetric key its data are
// under and, for each recipient, the key of the recipient's that the
// symmetric key is to be encrypted under.
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

// The envelope the sender's run, holding both recipients' keys, writes.
std::string TheEnvelope() {
  return EncryptEnvelopes(TheSendersInput(), "", Keys({kVendor, kUser}));
}

// The text a decrypting run of `envelope` produced holding `keys`.
std::string Produced(const std::string& envelope, const ProtectKeyList& keys) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = keys;
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

// The buffer the first key block of `envelope` records under `key`: the
// block's characters read out of the coding scheme and out of the key.
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

// §O.5: the design is encrypted under a symmetric key, the symmetric key
// under the recipient's public key and recorded in a key_block, the envelope
// can be created under either secret key scheme, and several key blocks open
// one envelope to several recipients.
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

// §O.5 against the flow: the sender's run writes one envelope with a key
// block for each recipient, the design in neither the clear nor either
// block; each recipient's run, holding only its own key, recovers the
// symmetric key from its block and the design with it, and a run holding
// neither recipient's key gets no design.
TEST(DigitalEnvelopes, EachRecipientOpensTheOneEnvelopeWithItsOwnKey) {
  std::string envelope = TheEnvelope();
  EXPECT_EQ(Count(envelope, kKeyBlockAnnouncement), 2u);
  EXPECT_FALSE(Holds(envelope, "result = 42"));
  EXPECT_TRUE(
      Holds(Produced(envelope, Keys({kVendor})), "initial result = 42;"));
  EXPECT_TRUE(Holds(Produced(envelope, Keys({kUser})), "initial result = 42;"));
  EXPECT_FALSE(Holds(Produced(envelope, ProtectKeyList()), "result = 42"));
}

// §O.5's example: the key encrypting the data block may be specified by the
// data_keyowner/data_keyname pair, which leaves the decrypting tool needing
// the key the pair names, or by data_decrypt_key, the key itself in the
// block, which the annex prefers for the dependency it removes and the
// hit-and-trial it defeats. That is what this tool writes: the buffer a
// recipient's key opens carries the data_method and the data_decrypt_key
// that open the data block, and neither the key nor the keyword carrying it
// stands in the clear.
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
