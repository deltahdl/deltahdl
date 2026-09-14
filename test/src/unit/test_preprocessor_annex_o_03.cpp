#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The one key of the scenario -- the vendor's secret, standing here for the
// key a vendor would embed -- and a key that is not it.
constexpr std::string_view kVendorKey = "vendor-secret-key";
constexpr std::string_view kOtherKey = "not-the-vendors-key";

// The text a decrypting run of `src` under `key` produced. An empty key is a
// run given no key at all.
std::string Produced(const std::string& src, std::string_view key) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_key = key;
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<test>", src));
}

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// §O.3: the key of the tool vendor secret key encryption system is the
// vendor's, embedded within the tool, and one key serves both encryption and
// decryption; the system is roughly equivalent to the historical `protect
// technique and is completely tool-vendor-specific.
TEST(ToolVendorSecretKeySystem, TheKeyIsTheVendorsEmbeddedAndSymmetric) {
  EXPECT_TRUE(ToolVendorSecretKeyIsEmbeddedInTheTool());
  EXPECT_TRUE(ToolVendorSecretKeyEncryptsAndDecrypts());
  EXPECT_TRUE(ToolVendorSecretKeySystemIsToolVendorSpecific());
  EXPECT_EQ(DirectiveTheToolVendorSecretKeySystemIsEquivalentTo(), "`protect");
}

// §O.3 against the flow: the IP author encrypts the IP under the one key,
// and an IP consumer's run of the same tool holding that key decrypts it --
// the same key doing both halves is what the scenario relies on. A run
// holding another key, as another vendor's tool would, gets no design out of
// the envelope.
TEST(ToolVendorSecretKeySystem,
     TheSameKeyEncryptsForTheAuthorAndDecryptsForTheConsumer) {
  std::string envelope = EncryptEnvelopes(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n",
      kVendorKey);
  EXPECT_FALSE(Holds(envelope, "result = 42"));
  EXPECT_TRUE(Holds(Produced(envelope, kVendorKey), "initial result = 42;"));
  EXPECT_FALSE(Holds(Produced(envelope, kOtherKey), "result = 42"));
}

// §O.3 as this tool has it: no vendor key is embedded, so a decrypting run
// that was given no key holds none and opens nothing -- the key the scenario
// embeds is, in this tool, the one both runs are given.
TEST(ToolVendorSecretKeySystem,
     ThisToolEmbedsNoKeyAndARunGivenNoneOpensNothing) {
  EXPECT_FALSE(ToolEmbedsAVendorSecretKey());
  std::string envelope = EncryptEnvelopes(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n",
      kVendorKey);
  EXPECT_FALSE(Holds(Produced(envelope, ""), "result = 42"));
}

}  // namespace
