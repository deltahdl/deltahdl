#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "parser/ast_type.h"

namespace delta {

struct ModuleItem;

void CheckStringNumericAssignments(
    const std::vector<ModuleItem*>& items,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const std::unordered_set<std::string_view>& arrays, DiagEngine& diag);

}  // namespace delta
