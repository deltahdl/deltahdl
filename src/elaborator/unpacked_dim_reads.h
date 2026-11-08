#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "parser/ast_type.h"

namespace delta {

struct ModuleDecl;

void CheckVariableReadsInUnpackedDims(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, DataTypeKind>& values,
    DiagEngine& diag);

}  // namespace delta
