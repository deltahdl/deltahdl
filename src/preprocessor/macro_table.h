#pragma once

#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/source_loc.h"

namespace delta {

struct MacroDef {
  std::string name;
  std::string body;
  std::vector<std::string> params;
  std::vector<std::string> param_defaults;  // Per-param default; empty = none.
  SourceLoc def_loc;
  bool is_function_like = false;
};

class MacroTable {
 public:
  void Define(MacroDef macro);
  void Undefine(std::string_view name);
  void UndefineAll();

  const MacroDef* Lookup(std::string_view name) const;
  bool IsDefined(std::string_view name) const;

 private:
  std::unordered_map<std::string, MacroDef> macros_;
};

}  // namespace delta
