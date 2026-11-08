#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kVendorKey = "vendor-secret-key";

constexpr std::string_view kDesign = "  initial result = 42;\n";
constexpr std::string_view kDecryptLicense =
    "`pragma protect decrypt_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"decrypt\")\n";
constexpr std::string_view kRuntimeLicense =
    "`pragma protect runtime_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"simulate\")\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

std::string TheInput() {
  std::string src = "module m;\n";
  src += "`pragma protect author=\"Acme Author\"\n";
  src += "`pragma protect author_info=\"revision 3\"\n";
  src += "`pragma protect data_keyowner=\"acme-eda\"\n";
  src += "`pragma protect data_keyname=\"vendor-2026\"\n";
  src += "`pragma protect digest_block\n";
  src += "`pragma protect begin\n";
  src.append(kDecryptLicense).append(kRuntimeLicense).append(kDesign);
  src += "`pragma protect end\n";
  src += "endmodule\n";
  return src;
}

std::string LineBeneath(std::string_view written, std::string_view block) {
  std::string opening = "`pragma protect ";
  opening.append(block).append("\n");
  size_t pos = written.find(opening);
  if (pos == std::string_view::npos) return "";
  size_t start = pos + opening.size();
  size_t close = written.find('\n', start);
  if (close == std::string_view::npos) close = written.size();
  return std::string(written.substr(start, close - start));
}

TEST(ToolVendorSecretKeyOutput, TheOutputIsAsTheAnnexHasIt) {
  EXPECT_TRUE(CleartextIsCopiedToTheToolVendorSecretKeyOutput());
  auto expressions = ExpressionsTheToolVendorSecretKeyOutputCarries();
  ASSERT_EQ(expressions.size(), 10u);
  EXPECT_EQ(expressions[0], "begin_protected");
  EXPECT_EQ(expressions[1], "data_keyowner");
  EXPECT_EQ(expressions[2], "data_keyname");
  EXPECT_EQ(expressions[3], "data_method");
  EXPECT_EQ(expressions[4], "encoding");
  EXPECT_EQ(expressions[5], "author");
  EXPECT_EQ(expressions[6], "author_info");
  EXPECT_EQ(expressions[7], "digest_block");
  EXPECT_EQ(expressions[8], "data_block");
  EXPECT_EQ(expressions[9], "end_protected");
  for (std::string_view name : expressions) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
  }
  auto composition = WhatTheToolVendorSecretKeyDataBlockIsComposedOf();
  ASSERT_EQ(composition.size(), 3u);
  EXPECT_EQ(composition[0], "decrypt_license");
  EXPECT_EQ(composition[1], "runtime_license");
}

TEST(ToolVendorSecretKeyOutput,
     TheRunGeneratesTheListedExpressionsForTheBlock) {
  std::string written = EncryptEnvelopes(TheInput(), kVendorKey);
  EXPECT_TRUE(Holds(written, "module m;\n"));
  EXPECT_TRUE(Holds(written, "endmodule\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect data_keyowner=\"acme-eda\"\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect data_keyname=\"vendor-2026\"\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect data_method=\""));
  EXPECT_TRUE(Holds(written, "`pragma protect encoding=("));
  EXPECT_TRUE(Holds(written, "`pragma protect author=\"Acme Author\"\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect author_info=\"revision 3\"\n"));
  EXPECT_FALSE(LineBeneath(written, "digest_block").empty());
  EXPECT_FALSE(LineBeneath(written, "data_block").empty());
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
}

TEST(ToolVendorSecretKeyOutput,
     TheDataAreTheLicencesAndTheTextBetweenBeginAndEnd) {
  std::string written = EncryptEnvelopes(TheInput(), kVendorKey);
  EXPECT_FALSE(Holds(written, "lic.so"));
  EXPECT_FALSE(Holds(written, "result = 42"));
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(LineBeneath(written, "data_block"),
                                     kVendorKey, &cleartext));
  std::string composed(kDecryptLicense);
  composed.append(kRuntimeLicense).append(kDesign);
  EXPECT_EQ(cleartext, composed);
}

}  // namespace
