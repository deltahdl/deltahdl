#include "preprocessor/standard_pragmas.h"

#include <algorithm>
#include <string_view>
#include <vector>

#include "preprocessor/protect_envelope.h"

namespace delta {

const std::vector<std::string_view>& RecognizedPragmaNames() {
  static const std::vector<std::string_view> kNames{kProtectPragmaName};
  return kNames;
}

bool IsRecognizedPragmaName(std::string_view name) {
  const auto& names = RecognizedPragmaNames();
  return std::find(names.begin(), names.end(), name) != names.end();
}

}  // namespace delta
