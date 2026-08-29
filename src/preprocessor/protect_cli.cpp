#include "preprocessor/protect_cli.h"

#include <iostream>
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

// Reports an option that was recognized and whose value the command line ended
// before, and records the refusal so the caller's parse fails.
void ReportMissingValue(std::string_view name, ProtectCliOptions& opts) {
  std::cerr << name << " expects a value\n";
  opts.rejected_argument = true;
}

}  // namespace

bool TryParseProtectArg(std::string_view arg, int& i, int argc,
                        const char* const argv[], ProtectCliOptions& opts) {
  if (arg == "--encrypt") {
    opts.encrypt = true;
    return true;
  }
  if (arg == "--protect-key") {
    if (i + 1 >= argc) {
      ReportMissingValue("--protect-key", opts);
      return true;
    }
    std::string_view key = argv[++i];
    // §34.5.10 gives an empty key no meaning, which is why AddNamedKey refuses
    // one written as the third part of a named key. The single exchange key is
    // refused on the same ground rather than stored as a key of nothing.
    if (key.empty()) {
      std::cerr << "--protect-key expects a key\n";
      opts.rejected_argument = true;
      return true;
    }
    opts.exchange_key = key;
    return true;
  }
  if (arg != "--protect-named-key") return false;
  if (i + 1 >= argc) {
    ReportMissingValue("--protect-named-key", opts);
    return true;
  }
  std::string_view value = argv[++i];
  if (!AddNamedKey(value, opts.keys)) {
    // §34.5.10 selects a key by the entity that owns it and the name it was
    // given, so all three parts of `<owner>:<name>=<key>` have to be there and
    // none of them empty. The value is named in the report because which part
    // was missing is not something the option's name says.
    std::cerr << "--protect-named-key expects <owner>:<name>=<key>: " << value
              << "\n";
    opts.rejected_argument = true;
  }
  return true;
}

}  // namespace delta
