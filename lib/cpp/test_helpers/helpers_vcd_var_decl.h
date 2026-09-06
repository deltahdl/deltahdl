#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "helpers_text_lines.h"

namespace delta {

// §21.7.2.1 (Syntax 21-20) spells a declaration
// "$var var_type size identifier_code reference $end", so a well-formed one
// tokenizes to six words. Returns the tokens of the declaration whose reference
// name is `name`, or an empty vector when the dump holds none. The identifier
// code is not matched on: it is assigned in registration order and says nothing
// about the object.
inline std::vector<std::string> VarDecl(const std::string& content,
                                        std::string_view name) {
  for (const auto& l : AllLines(content)) {
    auto toks = Tokens(l);
    if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) return toks;
  }
  return {};
}

// True when any $var declaration in the dump names `name`.
inline bool HasVar(const std::string& content, std::string_view name) {
  return !VarDecl(content, name).empty();
}

}  // namespace delta
