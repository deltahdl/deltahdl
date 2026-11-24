#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kVendorKey = "vendor-secret-key";
constexpr std::string_view kOtherKey = "not-the-vendors-key";

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

TEST(ToolVendorSecretKeySystem, TheKeyIsTheVendorsEmbeddedAndSymmetric) {
  EXPECT_TRUE(ToolVendorSecretKeyIsEmbeddedInTheTool());
  EXPECT_TRUE(ToolVendorSecretKeyEncryptsAndDecrypts());
  EXPECT_TRUE(ToolVendorSecretKeySystemIsToolVendorSpecific());
  EXPECT_EQ(DirectiveTheToolVendorSecretKeySystemIsEquivalentTo(), "`protect");
}

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

TEST(ToolVendorSecretKeySystem, ABlockAroundAWholeModuleIsSealedAndRecovered) {
  std::string envelope = EncryptEnvelopes(
      "`pragma protect begin\n"
      "module sealed_whole;\n"
      "endmodule\n"
      "`pragma protect end\n",
      kVendorKey);
  EXPECT_FALSE(Holds(envelope, "sealed_whole"));
  EXPECT_TRUE(Holds(Produced(envelope, kVendorKey),
                    "module sealed_whole;\nendmodule\n"));
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_key = kOtherKey;
  Preprocessor pp(mgr, diag, config);
  std::string refused = pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_FALSE(Holds(refused, "sealed_whole"));
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(envelope, "data_block") + 1, "34.3.2"));
}

}  // namespace
