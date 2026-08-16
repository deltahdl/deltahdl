#include "preprocessor/protect_cli.h"

#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {

namespace {

// A named key is written `<owner>:<name>=<key>`, which are the three things
// §34.5.10 needs to select one: whose keys these are, which of them this is,
// and the key itself. Answers false where either separator is missing, so a
// value that names no owner or no key is refused rather than stored as a key
// under an empty name.
bool AddNamedKey(std::string_view value, ProtectKeyList& keys) {
  auto colon = value.find(':');
  if (colon == std::string_view::npos) return false;
  auto eq = value.find('=', colon + 1);
  if (eq == std::string_view::npos) return false;
  std::string owner(value.substr(0, colon));
  std::string name(value.substr(colon + 1, eq - colon - 1));
  std::string key(value.substr(eq + 1));
  if (owner.empty() || name.empty() || key.empty()) return false;
  keys.Add({owner, name, key});
  return true;
}

}  // namespace

bool TryParseProtectArg(std::string_view arg, int& i, int argc,
                        const char* const argv[], ProtectCliOptions& opts) {
  if (arg == "--encrypt") {
    opts.encrypt = true;
    return true;
  }
  if (arg == "--protect-key" && i + 1 < argc) {
    opts.exchange_key = argv[++i];
    return true;
  }
  if (arg == "--protect-named-key" && i + 1 < argc) {
    return AddNamedKey(argv[++i], opts.keys);
  }
  return false;
}

}  // namespace delta
