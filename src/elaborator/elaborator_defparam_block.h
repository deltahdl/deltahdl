#pragma once

#include <string_view>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

const Stmt* FindBlockParamDecl(const RtlirModule& mod, const HierPath& blocks,
                               std::string_view name);

Expr* BlockParamInit(Expr* value, const ScopeMap& scope, Arena& arena);

}  // namespace delta
