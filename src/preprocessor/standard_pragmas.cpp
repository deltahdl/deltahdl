#include "preprocessor/standard_pragmas.h"

#include <algorithm>
#include <string_view>
#include <vector>

#include "preprocessor/protect_envelope.h"

namespace delta {

const std::vector<std::string_view>& RecognizedPragmaNames() {
  // §22.11.1: protect is the one pragma_name this implementation carries
  // pragma_keyword state for, so restoring it is the whole of what resetall
  // does here. reset and resetall are recognised as directives without holding
  // state of their own, so neither is a pragma either of them restores.
  static const std::vector<std::string_view> kNames{kProtectPragmaName};
  return kNames;
}

bool IsRecognizedPragmaName(std::string_view name) {
  const auto& names = RecognizedPragmaNames();
  return std::find(names.begin(), names.end(), name) != names.end();
}

}  // namespace delta
