#pragma once

// §23.10.1 with §23.10.2: a defparam may name a parameter declared in a named
// block, which is a statement of a procedure's body rather than one of the
// module's parameters. These find such a declaration and the initializer a
// defparam gives it.

#include <string_view>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

// The declaration of the parameter `name` in the named block `blocks` names,
// outermost first, within a procedure of `mod`; null where no procedure holds
// such a block or the block declares no such parameter.
const Stmt* FindBlockParamDecl(const RtlirModule& mod, const HierPath& blocks,
                               std::string_view name);

// The initializer a defparam's right-hand side `value` gives a block
// parameter, read in `scope`, the scope of the defparam statement: a literal
// stands in no scope and is kept as written, and any other constant expression
// is folded to an integer literal. Null where it does not fold.
Expr* BlockParamInit(Expr* value, const ScopeMap& scope, Arena& arena);

}  // namespace delta
