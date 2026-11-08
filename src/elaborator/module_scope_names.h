#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_type.h"

namespace delta {

struct ModuleScopeNames {
  std::unordered_set<std::string_view> declared;
  std::unordered_set<std::string_view> nets;
  std::unordered_map<std::string_view, SourceLoc> cont_targets;
  std::unordered_map<std::string_view, SourceLoc> proc_targets;
  std::unordered_set<std::string_view> initialized;
  UwireDrivers uwire_drivers;
  std::unordered_set<std::string_view> interconnects;
  std::unordered_map<std::string_view, SourceLoc> force_targets;
  std::unordered_map<std::string_view, DataTypeKind> var_types;
  std::unordered_map<std::string_view, std::string_view> class_var_types;
  std::unordered_set<std::string_view> scalar_vars;
  std::unordered_set<std::string_view> real_vars;
  std::unordered_set<std::string_view> real_params;
  std::unordered_map<std::string_view, VarSelectShape> select_shapes;
  std::unordered_set<std::string_view> class_vars;
};

}  // namespace delta
