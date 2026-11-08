#pragma once

#include "common/diagnostic.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;

void CheckInstanceLocalTypeAssignments(const ModuleDecl* decl,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag);

}  // namespace delta
