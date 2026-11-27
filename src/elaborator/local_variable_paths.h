#pragma once

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

void ReportPathsToUnreachableLocals(const ModuleDecl& decl, DiagEngine& diag);

}  // namespace delta
