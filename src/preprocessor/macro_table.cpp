#include "preprocessor/macro_table.h"

namespace delta {

void MacroTable::Define(MacroDef macro) {
  std::string key = macro.name;
  macros_.insert_or_assign(std::move(key), std::move(macro));
}

void MacroTable::Undefine(std::string_view name) {
  macros_.erase(std::string(name));
}

void MacroTable::UndefineAll() { macros_.clear(); }

const MacroDef* MacroTable::Lookup(std::string_view name) const {
  auto it = macros_.find(std::string(name));
  if (it == macros_.end()) {
    return nullptr;
  }
  return &it->second;
}

bool MacroTable::IsDefined(std::string_view name) const {
  return macros_.contains(std::string(name));
}

}  // namespace delta
