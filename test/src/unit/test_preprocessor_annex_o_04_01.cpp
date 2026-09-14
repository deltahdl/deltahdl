#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
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

// The design the author protects.
constexpr std::string_view kDesign = "  initial result = 42;\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// The tool's database, holding the author's key under the author's owner
// and name as §O.4 has the author provide it.
ProtectKeyList TheAuthorsKeyInTheDatabase() {
  ProtectKeyList keys;
  keys.Add({std::string(kAuthor), std::string(kAuthorsKeyName),
            std::string(kAuthorsKey)});
  return keys;
}

// The encrypting run over `src` with the author's key in the database, and
// whether the run reported an error in the input.
struct Encrypting {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string written;

  explicit Encrypting(const std::string& src) {
    uint32_t file_id = mgr.AddFile("<test>", src);
    written =
        EncryptEnvelopes(src, "", TheAuthorsKeyInTheDatabase(), &diag, file_id);
  }
};

// The text a decrypting run of `envelope` produced with the author's key in
// its database.
std::string Produced(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheAuthorsKeyInTheDatabase();
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

// The input's required pragmas: the provider's key name and the region.
std::string RequiredInput() {
  std::string src = "`pragma protect data_keyowner=\"";
  src.append(kAuthor).append("\"\n");
  src += "`pragma protect data_keyname=\"";
  src.append(kAuthorsKeyName).append("\"\n");
  src += "`pragma protect begin\n";
  src.append(kDesign);
  src += "`pragma protect end\n";
  return src;
}

// §O.4.1: the input requires data_keyname naming the provider's key and the
// begin and end around the regions, and may include the same eight pragmas
// §O.3.1's input may, data_method there naming a public/private encryption
// scheme beside its method specifier.
TEST(IpAuthorSecretKeyInput, TheRequiredAndOptionalPragmasAreTheAnnexs) {
  auto required = PragmasRequiredByIpAuthorSecretKeyInput();
  ASSERT_EQ(required.size(), 3u);
  EXPECT_EQ(required[0], "data_keyname");
  EXPECT_EQ(required[1], "begin");
  EXPECT_EQ(required[2], "end");
  auto optional = PragmasOptionalInIpAuthorSecretKeyInput();
  ASSERT_EQ(optional.size(), 8u);
  EXPECT_EQ(optional[3], "data_method");
  EXPECT_TRUE(IpAuthorSecretKeyDataMethodNamesAPublicPrivateScheme());
  for (std::string_view name : required) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
  }
  for (std::string_view name : optional) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
  }
}

// §O.4.1 against the flow: an input carrying the required pragmas -- the
// provider's key name, under the provider as its owner, and begin and end
// around the region -- is sealed under the author's key without a report,
// and a decrypting run holding that key in its database opens it.
TEST(IpAuthorSecretKeyInput,
     TheRequiredPragmasSealTheRegionUnderTheAuthorsKey) {
  Encrypting run(RequiredInput());
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.written, "result = 42"));
  EXPECT_TRUE(Holds(Produced(run.written), "initial result = 42;"));
}

// §O.4.1 as this tool has it: the optional data_method names a public/private
// encryption scheme, and this tool provides none of the three §34.5.11's
// table names, so an input naming rsa draws §34.5.11.2's report for an
// algorithm the implementation does not provide, one the table does not
// require of every implementation. The rest of the optional pragmas beside
// the required ones are accepted as §O.3.1's are.
TEST(IpAuthorSecretKeyInput, APublicPrivateSchemeIsReportedAsNotProvided) {
  EXPECT_FALSE(ToolProvidesAPublicPrivateEncryptionScheme());
  std::string src = "`pragma protect author=\"Acme Author\"\n";
  src += "`pragma protect author_info=\"revision 3\"\n";
  src += "`pragma protect data_method=\"rsa\"\n";
  src += RequiredInput();
  Encrypting run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma data_method asks for an encryption "
                            "algorithm this implementation does not provide: "
                            "rsa, which IEEE 1800-2023 Table 34-3 does not "
                            "require of every implementation",
                            LineHolding(src, "data_method"), "34.5.11.2"));
}

}  // namespace
