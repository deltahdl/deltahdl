#pragma once

#include <functional>

#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"

namespace delta {

using CovergroupExprVisitor = std::function<void(const Expr*)>;

void ForEachCovergroupExpr(const CovergroupDecl& group,
                           const CovergroupExprVisitor& fn);

}  // namespace delta
