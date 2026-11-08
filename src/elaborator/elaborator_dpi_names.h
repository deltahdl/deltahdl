#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct CompilationUnit;
struct ImportItem;
struct ModuleItem;

using DpiClassNames = std::unordered_set<std::string_view>;

void AddImportedTypedefs(const ImportItem& import_item,
                         const CompilationUnit* unit, TypedefMap& typedefs);

TypedefMap DpiScopeTypedefs(const std::vector<ModuleItem*>& items,
                            const CompilationUnit* unit,
                            const TypedefMap& outer);

DpiClassNames CollectDpiClassNames(
    const CompilationUnit* unit,
    const std::vector<const std::vector<ModuleItem*>*>& scopes);

DataType ResolveDpiTypeName(const DataType& type, const TypedefMap& typedefs);

bool NamesAClass(const DataType& type, const TypedefMap& typedefs,
                 const DpiClassNames& classes);

}  // namespace delta
