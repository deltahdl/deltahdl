#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_directives.h"
#include "helpers_protect_license.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthor = "acme-ip";
constexpr std::string_view kAuthorsKeyName = "acme-2026";
constexpr std::string_view kAuthorsKey = "acme-private-key-material";

constexpr std::string_view kInsideTheBlock =
    "`pragma protect decrypt_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"decrypt\")\n"
    "`pragma protect runtime_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"simulate\")\n"
    "  initial result = 42;\n";

ProtectKeyList TheAuthorsKeyInTheDatabase() {
  ProtectKeyList keys;
  keys.Add({std::string(kAuthor), std::string(kAuthorsKeyName),
            std::string(kAuthorsKey)});
  return keys;
}

std::string TheOutput() {
  std::string src = "module m;\n";
  src += "`pragma protect author=\"Acme Author\"\n";
  src += "`pragma protect author_info=\"revision 3\"\n";
  src += "`pragma protect data_keyowner=\"";
  src.append(kAuthor).append("\"\n");
  src += "`pragma protect data_keyname=\"";
  src.append(kAuthorsKeyName).append("\"\n");
  src += "`pragma protect digest_block\n";
  src += "`pragma protect begin\n";
  src.append(kInsideTheBlock);
  src += "`pragma protect end\n";
  src += "endmodule\n";
  return EncryptEnvelopes(src, "", TheAuthorsKeyInTheDatabase());
}

size_t Count(std::string_view written, std::string_view needle) {
  size_t count = 0;
  for (size_t pos = written.find(needle); pos != std::string_view::npos;
       pos = written.find(needle, pos + needle.size())) {
    ++count;
  }
  return count;
}

std::string Recovered(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheAuthorsKeyInTheDatabase();
  config.ask_license = GrantingEveryLicence();
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

TEST(IpAuthorSecretKeyOutput,
     TheOutputIsTheToolVendorSystemsWithTheAuthorsKey) {
  EXPECT_TRUE(CleartextIsCopiedToTheIpAuthorSecretKeyOutput());
  auto expressions = ExpressionsTheIpAuthorSecretKeyOutputCarries();
  auto vendor = ExpressionsTheToolVendorSecretKeyOutputCarries();
  ASSERT_EQ(expressions.size(), vendor.size());
  for (size_t i = 0; i < expressions.size(); ++i) {
    EXPECT_EQ(expressions[i], vendor[i]);
    EXPECT_TRUE(IsProtectPragmaKeyword(expressions[i])) << expressions[i];
  }
  auto composition = WhatTheIpAuthorSecretKeyDataBlockIsComposedOf();
  ASSERT_EQ(composition.size(), 3u);
  EXPECT_EQ(composition[0], "decrypt_license");
  EXPECT_EQ(composition[1], "runtime_license");
  EXPECT_TRUE(IpAuthorSecretKeyOutputNamesThePublicPrivateSchemeAsItsMethod());
}

TEST(IpAuthorSecretKeyOutput, TheRunGeneratesTheListedExpressionsForTheBlock) {
  std::string written = TheOutput();
  EXPECT_EQ(Count(written, "module m;\n"), 1u);
  EXPECT_EQ(Count(written, "endmodule\n"), 1u);
  const std::string_view kExpressions[] = {
      "`pragma protect begin_protected\n",
      "`pragma protect data_keyowner=\"acme-ip\"\n",
      "`pragma protect data_keyname=\"acme-2026\"\n",
      "`pragma protect data_method=\"",
      "`pragma protect encoding=(",
      "`pragma protect author=\"Acme Author\"\n",
      "`pragma protect author_info=\"revision 3\"\n",
      "`pragma protect digest_block\n",
      "`pragma protect data_block\n",
      "`pragma protect end_protected\n",
  };
  for (std::string_view expression : kExpressions) {
    EXPECT_GE(Count(written, expression), 1u) << expression;
  }
}

TEST(IpAuthorSecretKeyOutput,
     TheDataAreTheLicencesAndTheTextUnderTheAuthorsKey) {
  std::string written = TheOutput();
  EXPECT_EQ(Count(written, "lic.so"), 0u);
  EXPECT_EQ(Count(written, "result = 42"), 0u);
  EXPECT_EQ(Count(Recovered(written), "  initial result = 42;\n"), 1u);
  EXPECT_FALSE(ToolProvidesAPublicPrivateEncryptionScheme());
  EXPECT_EQ(Count(written, "data_method=\"rsa\""), 0u);
}

constexpr std::string_view kAuthorsNames =
    "`pragma protect data_keyowner=\"acme-ip\"\n"
    "`pragma protect data_keyname=\"acme-2026\"\n";

TEST(IpAuthorSecretKeyOutput, ARegionOfAnUnnamedAuthorNamesNone) {
  std::string src(kAuthorsNames);
  src += "`pragma protect begin\n  initial result = 42;\n";
  src += "`pragma protect end\n";
  std::string written = EncryptEnvelopes(src, "", TheAuthorsKeyInTheDatabase());
  EXPECT_EQ(ProtectDirectiveCount(written, "data_block"), 1u);
  EXPECT_EQ(ProtectDirectiveCount(written, "author"), 0u);
  EXPECT_EQ(ProtectDirectiveCount(written, "author_info"), 0u);
}

TEST(IpAuthorSecretKeyOutput, TheDigestAndTheDataStandBeneathTheirKeywords) {
  std::string written = TheOutput();
  std::string region =
      written.substr(ProtectDirectiveAt(written, "begin_protected"));
  std::string cleartext;
  EXPECT_TRUE(DecryptProtectedRegion(ProtectBlockBeneath(region, "data_block"),
                                     kAuthorsKey, &cleartext));
  EXPECT_EQ(cleartext, kInsideTheBlock);
  std::string digest = ProtectBlockBeneath(region, "digest_block");
  EXPECT_FALSE(digest.empty());
  EXPECT_EQ(Count(digest, "`pragma"), 0u);
  EXPECT_NE(digest, ProtectBlockBeneath(region, "data_block"));
}

TEST(IpAuthorSecretKeyOutput, EachBlockGetsARegionAroundTheCleartext) {
  std::string written = EncryptEnvelopes(
      WithTwoProtectBlocks(kAuthorsNames, "  initial first = 42;\n",
                           "  initial second = 57;\n"),
      "", TheAuthorsKeyInTheDatabase());
  EXPECT_EQ(Count(written, "initial"), 0u);
  EXPECT_TRUE(HoldsTwoRegionsAroundTheCleartext(written));
  EXPECT_TRUE(
      TextsInOrder(Recovered(written), {"initial first = 42;", "wire between;",
                                        "initial second = 57;", "endmodule"}));
}

}  // namespace
