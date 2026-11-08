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

constexpr std::string_view kAuthor = "acme-ip";
constexpr std::string_view kAuthorsKeyName = "acme-2026";
constexpr std::string_view kAuthorsKey = "acme-private-key-material";

constexpr std::string_view kDesign = "  initial result = 42;\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

ProtectKeyList TheAuthorsKeyInTheDatabase() {
  ProtectKeyList keys;
  keys.Add({std::string(kAuthor), std::string(kAuthorsKeyName),
            std::string(kAuthorsKey)});
  return keys;
}

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

std::string Produced(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheAuthorsKeyInTheDatabase();
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

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

TEST(IpAuthorSecretKeyInput,
     TheRequiredPragmasSealTheRegionUnderTheAuthorsKey) {
  Encrypting run(RequiredInput());
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.written, "result = 42"));
  EXPECT_TRUE(Holds(Produced(run.written), "initial result = 42;"));
}

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
