#pragma once

#include "common/source_loc.h"

#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace delta {

struct MacroDef {
    std::string name;
    std::string body;
    std::vector<std::string> params;
    SourceLoc def_loc;
    bool is_function_like = false;
};

class MacroTable {
  public:
    void define(MacroDef macro);
    void undefine(std::string_view name);
    void undefine_all();

    const MacroDef* lookup(std::string_view name) const;
    bool is_defined(std::string_view name) const;

  private:
    std::unordered_map<std::string, MacroDef> macros_;
};

} // namespace delta
