#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;

void CheckContinuousPropertyWrites(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, std::string_view>& handle_types,
    const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
