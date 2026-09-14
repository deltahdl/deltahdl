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

// The IP author, the name the author's key is provided under, and the key
// itself; and a second party whose key a tool might hold instead.
constexpr std::string_view kAuthor = "acme-ip";
constexpr std::string_view kAuthorsKeyName = "acme-2026";
constexpr std::string_view kAuthorsKey = "acme-private-key-material";
constexpr std::string_view kOtherParty = "globex-ip";
constexpr std::string_view kOtherPartysKeyName = "globex-2026";
constexpr std::string_view kOtherPartysKey = "globex-private-key-material";

// The design the author protects.
constexpr std::string_view kDesign = "  initial result = 42;\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// A database holding one party's key under that party's owner and name.
ProtectKeyList DatabaseHolding(std::string_view owner, std::string_view name,
                               std::string_view key) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(name), std::string(key)});
  return keys;
}

// The author's input: the region designates the author's key by owner and
// name, as §34.5.10 and §34.5.12 have it designated.
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

// The text a decrypting run of `envelope` produced with `database` as the
// keys it holds.
std::string Produced(const std::string& envelope,
                     const ProtectKeyList& database) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = database;
  Preprocessor pp(mgr, diag, config);
  return pp.Preprocess(mgr.AddFile("<envelope>", envelope));
}

// §O.4: the IP is encrypted with the author's public key, the decrypting
// tool holds the author's private key in its secure key database, and the
// authors provide their private keys to the tools' database.
TEST(IpAuthorSecretKeySystem, TheAuthorsKeyPairIsWhatEncryptsAndDecrypts) {
  EXPECT_TRUE(IpAuthorSecretKeyEncryptsWithTheAuthorsPublicKey());
  EXPECT_TRUE(IpAuthorSecretKeyDecryptsWithThePrivateKeyInTheToolsDatabase());
  EXPECT_TRUE(IpAuthorsProvideTheirPrivateKeysToTheToolsDatabase());
}

// §O.4 against the flow: the author's key, provided to the decrypting run
// under the author's owner and name, is the tool's database, and a run
// holding it opens the design the author sealed under that key; a run whose
// database holds another party's key, or none, does not.
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

// §O.4 as this tool has it: the algorithm is §34.3.1's symmetric one, so the
// key the database holds under the author's name is the key the author
// encrypted under and no second key of a pair is derived from it -- a
// database holding a different key under the author's own owner and name
// opens nothing.
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
