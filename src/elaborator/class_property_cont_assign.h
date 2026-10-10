#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;

// §6.21 (printed page 134): a non-static class property exists only in an
// object created at run time, so no continuous assignment and no procedural
// continuous assignment (`assign` or `force` in a procedure) may write one.
// Reports each such assignment in the module `decl` whose target is reached
// through a class handle, `h.x`, `h.x[0]` or `h.s.f`, alone or inside a
// concatenation, and names a property its class declares without `static`.
// `handle_types` gives each handle variable's class name.
void CheckContinuousPropertyWrites(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, std::string_view>& handle_types,
    const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
