#include <gtest/gtest.h>

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

constexpr std::string_view kAuthor = "acme-ip";
constexpr std::string_view kAuthorsKeyName = "acme-2026";
constexpr std::string_view kAuthorsKey = "acme-private-key-material";
constexpr std::string_view kOtherParty = "globex-ip";
constexpr std::string_view kOtherPartysKeyName = "globex-2026";
constexpr std::string_view kOtherPartysKey = "globex-private-key-material";

constexpr std::string_view kDesign = "  initial result = 42;\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

ProtectKeyList DatabaseHolding(std::string_view owner, std::string_view name,
                               std::string_view key) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(name), std::string(key)});
  return keys;
}

std::string TheAuthorsInput() {
  std::string src = "`pragma protect data_keyowner=\"";
  src.append(kAuthor).append("\"\n");
  src += "`pragma protect data_keyname=\"";
  src.append(kAuthorsKeyName).append("\"\n");
  src += "`pragma protect begin\n";
  src.append(kDesign);
  src += "`pragma protect end\n";
  return src;
}

std::string Produced(const std::string& envelope,
                     const ProtectKeyList& database) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = database;
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

TEST(IpAuthorSecretKeySystem, TheAuthorsKeyPairIsWhatEncryptsAndDecrypts) {
  EXPECT_TRUE(IpAuthorSecretKeyEncryptsWithTheAuthorsPublicKey());
  EXPECT_TRUE(IpAuthorSecretKeyDecryptsWithThePrivateKeyInTheToolsDatabase());
  EXPECT_TRUE(IpAuthorsProvideTheirPrivateKeysToTheToolsDatabase());
}

TEST(IpAuthorSecretKeySystem, TheKeyProvidedToTheToolsDatabaseOpensTheDesign) {
  EXPECT_TRUE(ToolsKeyDatabaseIsTheKeysGivenToTheRun());
  ProtectKeyList authors =
      DatabaseHolding(kAuthor, kAuthorsKeyName, kAuthorsKey);
  std::string envelope = EncryptEnvelopes(TheAuthorsInput(), "", authors);
  EXPECT_FALSE(Holds(envelope, "result = 42"));
  EXPECT_TRUE(Holds(Produced(envelope, authors), "initial result = 42;"));
  ProtectKeyList others =
      DatabaseHolding(kOtherParty, kOtherPartysKeyName, kOtherPartysKey);
  EXPECT_FALSE(Holds(Produced(envelope, others), "result = 42"));
  EXPECT_FALSE(Holds(Produced(envelope, ProtectKeyList()), "result = 42"));
}

TEST(IpAuthorSecretKeySystem, TheDatabaseHoldsTheKeyTheAuthorEncryptedUnder) {
  EXPECT_FALSE(ToolDerivesADecryptionKeyFromTheAuthorsEncryptionKey());
  std::string envelope =
      EncryptEnvelopes(TheAuthorsInput(), "",
                       DatabaseHolding(kAuthor, kAuthorsKeyName, kAuthorsKey));
  ProtectKeyList another_under_the_authors_name =
      DatabaseHolding(kAuthor, kAuthorsKeyName, kOtherPartysKey);
  EXPECT_FALSE(
      Holds(Produced(envelope, another_under_the_authors_name), "result = 42"));
}

}  // namespace
