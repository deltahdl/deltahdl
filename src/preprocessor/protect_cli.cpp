#include "preprocessor/protect_cli.h"

#include <iostream>
#include <string>
#include <string_view>

#include "common/arg_origin.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

namespace {

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

void ReportMissingValue(std::string_view name, int i, ProtectCliOptions& opts) {
  std::cerr << ArgOriginPrefix(opts.arg_origins, i) << name
            << " expects a value\n";
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
      ReportMissingValue("--protect-key", i, opts);
      return true;
    }
    std::string_view key = argv[++i];
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
    ReportMissingValue("--protect-named-key", i, opts);
    return true;
  }
  std::string_view value = argv[++i];
  if (!AddNamedKey(value, opts.keys)) {
    std::cerr << "--protect-named-key expects <owner>:<name>=<key>: " << value
              << "\n";
    opts.rejected_argument = true;
  }
  return true;
}

}  // namespace delta
