#pragma once

#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

void CollectScopeBases(const Expr* e, std::vector<const Expr*>& out);

void CollectProcScopeBases(const Stmt* s, std::vector<const Expr*>& out);

}  // namespace delta
