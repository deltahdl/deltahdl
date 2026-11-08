#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kKeyBlockDirective =
    "`pragma protect key_block=\"NOTAKEYBLOCKOFANYENVELOPE\"\n";

constexpr std::string_view kEncodingSealedDesign = "  initial result = 42;\n";

constexpr std::string_view kFirstProvider = "aegis-custody";
constexpr std::string_view kFirstProviderKeyName = "wrapping-2026";
constexpr std::string_view kFirstProviderKey = "aegis-custody-wrapping-key";
constexpr std::string_view kSecondProvider = "borealis-trust";
constexpr std::string_view kSecondProviderKeyName = "wrapping-2027";
constexpr std::string_view kSecondProviderKey = "borealis-trust-wrapping-key";
constexpr std::string_view kThirdProvider = "cerulean-vault";
constexpr std::string_view kThirdProviderKeyName = "wrapping-2028";
constexpr std::string_view kThirdProviderKey = "cerulean-vault-wrapping-key";

ProtectKeyList KeysOfEveryProvider() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstProvider, kFirstProviderKeyName, kFirstProviderKey));
  keys.Add(KeyOf(kSecondProvider, kSecondProviderKeyName, kSecondProviderKey));
  keys.Add(KeyOf(kThirdProvider, kThirdProviderKeyName, kThirdProviderKey));
  return keys;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Designation(std::string_view provider, std::string_view key_name,
                        std::string_view data_key_name) {
  std::string text = Writes("key_keyowner", provider);
  text.append(Writes("data_keyname", data_key_name));
  text.append(Writes("key_keyname", key_name));
  return text;
}

std::string Region(std::string_view described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kEncodingSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

struct KeyedEncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit KeyedEncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, KeysOfEveryProvider(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

TEST(ProtectKeyBlockEncryptionInput, ABlockContainedByNothingIsReported) {
  std::string src = "module m;\n";
  src.append(kKeyBlockDirective);
  src.append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "key_block is written where no previously", 2,
                            "34.5.27"));
}

TEST(ProtectKeyBlockEncryptionInput, ABlockASealedModelContainsIsIgnored) {
  std::string src = "`pragma protect begin_protected\n";
  src.append(kKeyBlockDirective);
  src.append("`pragma protect end_protected\n");
  EncryptionRun run(src);
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectKeyBlockEncryptionInput, ABlockInsideARegionToSealIsReported) {
  std::string src = Region(kKeyBlockDirective);
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "key_block is written where no previously", 2,
                            "34.5.27"));
}

TEST(ProtectKeyBlockEncryptionInput, TwoBlocksAgreeingAboutTheDataAreAccepted) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2026"));
  KeyedEncryptionRun run(Region(described));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect key_block"), 2U);
}

TEST(ProtectKeyBlockEncryptionInput,
     ADataExpressionChangedBetweenTwoBlocksIsReported) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2027"));
  std::string src = Region(described);
  KeyedEncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data decryption expressions change value",
      LineHolding(src, kSecondProviderKeyName), "34.5.27"));
}

TEST(ProtectKeyBlockEncryptionInput, EachOtherDataExpressionIsHeldToAgreeing) {
  const std::pair<std::string, std::string> kChanges[] = {
      {Writes("data_method", "des-cbc"),
       Writes("data_method", "x-deltahdl-stream")},
      {Writes("data_keyowner", "acme"), Writes("data_keyowner", "globex")},
      {"`pragma protect data_public_key\nYWNtZQ\n",
       "`pragma protect data_public_key\nZ2xvYmV4\n"}};
  for (const auto& [first, second] : kChanges) {
    std::string described = first;
    described.append(
        Designation(kFirstProvider, kFirstProviderKeyName, "design-2026"));
    described.append(second);
    described.append(
        Designation(kSecondProvider, kSecondProviderKeyName, "design-2026"));
    std::string src = Region(described);
    KeyedEncryptionRun run(src);
    EXPECT_TRUE(ReportedError(
        run.diag.Diagnostics(), "data decryption expressions change value",
        LineHolding(src, kSecondProviderKeyName), "34.5.27"))
        << first;
  }
}

TEST(ProtectKeyBlockEncryptionInput, TheReportedRegionIsStillGivenItsBlocks) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2027"));
  KeyedEncryptionRun run(Region(described));
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect key_block"), 2U);
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectKeyBlockEncryptionInput,
     AThirdDisagreeingBlockDrawsNoSecondReport) {
  std::string described =
      Designation(kFirstProvider, kFirstProviderKeyName, "design-2026");
  described.append(
      Designation(kSecondProvider, kSecondProviderKeyName, "design-2027"));
  described.append(
      Designation(kThirdProvider, kThirdProviderKeyName, "design-2028"));
  std::string src = Region(described);
  KeyedEncryptionRun run(src);
  EXPECT_EQ(run.diag.ErrorCount(), 1U);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data decryption expressions change value",
      LineHolding(src, kSecondProviderKeyName), "34.5.27"));
}

}  // namespace
