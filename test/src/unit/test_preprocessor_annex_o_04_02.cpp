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

// The IP author, the name the author's key is provided under, and the key.
constexpr std::string_view kAuthor = "acme-ip";
constexpr std::string_view kAuthorsKeyName = "acme-2026";
constexpr std::string_view kAuthorsKey = "acme-private-key-material";

// What the block holds: the two licences, then the design.
constexpr std::string_view kInsideTheBlock =
    "`pragma protect decrypt_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"decrypt\")\n"
    "`pragma protect runtime_license=(library=\"lic.so\", "
    "entry=\"acquire\", feature=\"simulate\")\n"
    "  initial result = 42;\n";

// The tool's database, holding the author's key under the author's owner
// and name.
ProtectKeyList TheAuthorsKeyInTheDatabase() {
  ProtectKeyList keys;
  keys.Add({std::string(kAuthor), std::string(kAuthorsKeyName),
            std::string(kAuthorsKey)});
  return keys;
}

// The output the encrypting run generates for an input of §O.4.1 with a
// cleartext section on either side of its one block, the block naming the
// provider's key under the provider, asking for a digest, and holding the
// licences and the design.
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

// How many times `written` carries `needle`.
size_t Count(std::string_view written, std::string_view needle) {
  size_t count = 0;
  for (size_t pos = written.find(needle); pos != std::string_view::npos;
       pos = written.find(needle, pos + needle.size())) {
    ++count;
  }
  return count;
}

// The text a decrypting run of `envelope` produced with the author's key in
// its database, where the data the block recorded come back as the source
// the compilation step reads.
std::string Recovered(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheAuthorsKeyInTheDatabase();
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

// §O.4.2: the output is the one §O.3.2 has the tool generate -- the cleartext
// copied, the same ten expressions for each block, the data composed of the
// licences and the text between begin and end -- with the key name the
// provider's and the method the public/private scheme's name.
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

// §O.4.2 against the flow: the encrypting run holding the author's key in
// its database copies the cleartext on either side of the block and
// generates for the block a protected region carrying each listed
// expression in the clear, the key's owner being the author and the key's
// name the provider's, with the digest and the data blocks announced by
// their keywords standing alone. The designations the input wrote ahead of
// the block are cleartext the run copies as well, so an expression may stand
// more than once; what the annex has is that the region generated carries
// it.
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

// §O.4.2 against the flow: the data the block records under the author's
// key are the two licences and the text between begin and end, none in the
// clear, and a decrypting run holding the author's key gets the design back
// where the block stood. The method the output names is the cipher this
// tool sealed the block with rather than a public/private scheme, this tool
// providing none.
TEST(IpAuthorSecretKeyOutput,
     TheDataAreTheLicencesAndTheTextUnderTheAuthorsKey) {
  std::string written = TheOutput();
  EXPECT_EQ(Count(written, "lic.so"), 0u);
  EXPECT_EQ(Count(written, "result = 42"), 0u);
  EXPECT_EQ(Count(Recovered(written), "  initial result = 42;\n"), 1u);
  EXPECT_FALSE(ToolProvidesAPublicPrivateEncryptionScheme());
  EXPECT_EQ(Count(written, "data_method=\"rsa\""), 0u);
}

}  // namespace
