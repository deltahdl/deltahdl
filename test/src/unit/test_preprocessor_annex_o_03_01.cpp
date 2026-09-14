#include <gtest/gtest.h>

#include <cstdint>
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

// The key standing in for the tool's embedded one, and the name the input
// designates it by.
constexpr std::string_view kVendorKey = "vendor-secret-key";
constexpr std::string_view kKeyName = "vendor-2026";

// The design the input asks to have encrypted.
constexpr std::string_view kDesign = "  initial result = 42;\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// The encrypting run over `src` under the vendor's key, with whether the run
// reported an error in the input.
struct Encrypting {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string written;

  explicit Encrypting(const std::string& src) {
    uint32_t file_id = mgr.AddFile("<test>", src);
    written =
        EncryptEnvelopes(src, kVendorKey, ProtectKeyList(), &diag, file_id);
  }
};

// The text a decrypting run of `envelope` under the vendor's key produced,
// which is where the design an input asked to have encrypted comes back: the
// run reads the envelope by its own description -- the cipher and the coding
// scheme the input chose -- and puts the recovered text where the envelope
// stood.
std::string Recovered(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_key = kVendorKey;
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

// §O.3.1: the input requires data_keyname, naming an embedded key, and the
// begin and end surrounding the regions to be encrypted; it may include eight
// more. Every name of both lists is a keyword §34.4 tabulates for the protect
// pragma, and no name is on both lists.
TEST(ToolVendorSecretKeyInput, TheRequiredAndOptionalPragmasAreTheAnnexs) {
  auto required = PragmasRequiredByToolVendorSecretKeyInput();
  ASSERT_EQ(required.size(), 3u);
  EXPECT_EQ(required[0], "data_keyname");
  EXPECT_EQ(required[1], "begin");
  EXPECT_EQ(required[2], "end");
  auto optional = PragmasOptionalInToolVendorSecretKeyInput();
  ASSERT_EQ(optional.size(), 8u);
  EXPECT_EQ(optional[0], "author");
  EXPECT_EQ(optional[1], "author_info");
  EXPECT_EQ(optional[2], "data_keyowner");
  EXPECT_EQ(optional[3], "data_method");
  EXPECT_EQ(optional[4], "encoding");
  EXPECT_EQ(optional[5], "digest_block");
  EXPECT_EQ(optional[6], "decrypt_license");
  EXPECT_EQ(optional[7], "runtime_license");
  for (std::string_view name : required) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
    for (std::string_view other : optional) EXPECT_NE(name, other);
  }
  for (std::string_view name : optional) {
    EXPECT_TRUE(IsProtectPragmaKeyword(name)) << name;
  }
}

// §O.3.1 against the flow: an input carrying only the required pragmas -- the
// key name, and begin and end around the region -- is a complete input to
// the encrypting run, which encrypts the region under the key the name
// stands for without reporting anything.
TEST(ToolVendorSecretKeyInput, TheRequiredPragmasAloneAreACompleteInput) {
  std::string src = "`pragma protect data_keyname=\"";
  src.append(kKeyName).append("\"\n");
  src += "`pragma protect begin\n";
  src.append(kDesign);
  src += "`pragma protect end\n";
  Encrypting run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.written, "result = 42"));
  EXPECT_TRUE(Holds(Recovered(run.written), kDesign));
}

// §O.3.1 against the flow: the eight optional pragmas may be included, and
// an input including all of them beside the required ones is accepted and
// encrypted the same way.
TEST(ToolVendorSecretKeyInput, TheOptionalPragmasMayBeIncluded) {
  std::string src = "`pragma protect author=\"Acme Author\"\n";
  src += "`pragma protect author_info=\"revision 3\"\n";
  src += "`pragma protect data_keyowner=\"acme-eda\"\n";
  src += "`pragma protect data_keyname=\"";
  src.append(kKeyName).append("\"\n");
  src += "`pragma protect data_method=\"des-cbc\"\n";
  src += "`pragma protect encoding=(enctype=\"base64\")\n";
  src += "`pragma protect digest_block\n";
  src +=
      "`pragma protect decrypt_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"decrypt\")\n";
  src +=
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"simulate\")\n";
  src += "`pragma protect begin\n";
  src.append(kDesign);
  src += "`pragma protect end\n";
  Encrypting run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.written, "result = 42"));
  EXPECT_TRUE(Holds(Recovered(run.written), kDesign));
}

}  // namespace
