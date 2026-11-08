#pragma once

#include <string>
#include <string_view>
#include <unordered_map>

#include "elaborator/type_eval.h"

namespace delta {

struct CompilationUnit;
struct DataType;
struct ModuleItem;

struct NettypeResolutionTarget {
  const ModuleItem* fn = nullptr;
  bool is_class_method = false;
  bool is_static_method = false;
  bool scope_named_nothing = false;
};

NettypeResolutionTarget FindNettypeResolutionFunction(
    const ModuleItem* item, const CompilationUnit* unit,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const TypedefMap& typedefs);

std::string NettypeScopeText(const DataType& scope);

}  // namespace delta
