#pragma once

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
  std::vector<std::string> param_defaults;
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

  // §5.6.1: the backslash of an escaped identifier is no part of it, so the
  // text macro names `\cpu3` and `cpu3` are one name. The table keeps and
  // seeks every name as this gives it, without the backslash.
  static std::string Key(std::string_view name);

 private:
  std::unordered_map<std::string, MacroDef> macros_;
};

}  // namespace delta
