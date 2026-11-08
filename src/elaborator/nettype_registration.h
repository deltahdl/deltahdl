#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "elaborator/type_eval.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct ModuleItem;

struct NettypeTables {
  std::unordered_set<std::string_view>& names;
  std::unordered_map<std::string_view, std::string_view>& resolve_funcs;
  std::unordered_map<std::string_view, std::string_view>& canonical;
};

void RegisterNettype(const ModuleItem& item, std::string_view key,
                     std::string_view home, const NettypeTables& tables,
                     Arena& arena);

void CopyNettype(std::string_view from, std::string_view to,
                 TypedefMap& typedefs, const NettypeTables& tables);

void RegisterPackageNettypes(const CompilationUnit* unit, TypedefMap& typedefs,
                             const NettypeTables& tables, Arena& arena);

}  // namespace delta
