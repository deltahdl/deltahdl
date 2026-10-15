#pragma once

#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

// Collects every scope-resolution member access (`base::member`, marked
// is_scope_resolution by the parser) whose base is a plain identifier,
// recursing through the whole expression tree so nested forms (`a::b::c`,
// scope refs inside calls/concats) are reached. System scopes (`$unit::`,
// `$root.`) carry their prefix in scope_prefix and are skipped here.
void CollectScopeBases(const Expr* e, std::vector<const Expr*>& out);

// Walks a procedural block, collecting scope-resolution bases from the RHS of
// every blocking/nonblocking assignment.
void CollectProcScopeBases(const Stmt* s, std::vector<const Expr*>& out);

}  // namespace delta
