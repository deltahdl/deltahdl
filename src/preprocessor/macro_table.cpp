#include "preprocessor/macro_table.h"

#include <string>
#include <string_view>
#include <utility>

namespace delta {

std::string MacroTable::Key(std::string_view name) {
  if (name.starts_with('\\')) name.remove_prefix(1);
  return std::string(name);
}

void MacroTable::Define(MacroDef macro) {
  macro.name = Key(macro.name);
  std::string key = macro.name;
  macros_.insert_or_assign(std::move(key), std::move(macro));
}

void MacroTable::Undefine(std::string_view name) { macros_.erase(Key(name)); }

void MacroTable::UndefineAll() { macros_.clear(); }

const MacroDef* MacroTable::Lookup(std::string_view name) const {
  auto it = macros_.find(Key(name));
  if (it == macros_.end()) {
    return nullptr;
  }
  return &it->second;
}

bool MacroTable::IsDefined(std::string_view name) const {
  return macros_.contains(Key(name));
}

}  // namespace delta
