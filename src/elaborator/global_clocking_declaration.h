#pragma once

#include <vector>

#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

bool ModuleDeclaresGlobalClocking(const ModuleDecl* decl);

const std::vector<EventExpr>* ModuleGlobalClockingEvent(const ModuleDecl* decl);

}  // namespace delta
