#pragma once

#include <vector>

#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// §14.14: true when `decl` itself contains a global clocking declaration.
bool ModuleDeclaresGlobalClocking(const ModuleDecl* decl);

// §16.5.2: the clocking event of the global clocking declaration `decl` itself
// contains, or null when it declares none. This is the event a $global_clock
// leading clocking event stands for.
const std::vector<EventExpr>* ModuleGlobalClockingEvent(const ModuleDecl* decl);

}  // namespace delta
