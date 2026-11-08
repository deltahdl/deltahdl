#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "helpers_text_lines.h"

namespace delta {

inline std::vector<std::string> VarDecl(const std::string& content,
                                        std::string_view name) {
  for (const auto& l : AllLines(content)) {
    auto toks = Tokens(l);
    if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) return toks;
  }
  return {};
}

inline bool HasVar(const std::string& content, std::string_view name) {
  return !VarDecl(content, name).empty();
}

}  // namespace delta
