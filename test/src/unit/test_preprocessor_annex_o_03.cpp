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

}  // namespace
