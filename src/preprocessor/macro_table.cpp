#include "preprocessor/macro_table.h"

namespace delta {

void MacroTable::define(MacroDef macro) {
    std::string key = macro.name;
    macros_.insert_or_assign(std::move(key), std::move(macro));
}

void MacroTable::undefine(std::string_view name) {
    macros_.erase(std::string(name));
}

void MacroTable::undefine_all() {
    macros_.clear();
}

const MacroDef* MacroTable::lookup(std::string_view name) const {
    auto it = macros_.find(std::string(name));
    if (it == macros_.end()) {
        return nullptr;
    }
    return &it->second;
}

bool MacroTable::is_defined(std::string_view name) const {
    return macros_.contains(std::string(name));
}

} // namespace delta
