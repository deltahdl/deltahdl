#pragma once

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

Expr* ActualInInstantiatingScope(Expr* actual, const std::string& parent_prefix,
                                 Arena& arena);

std::vector<EventExpr> ClockInInstantiatingScope(
    const std::vector<EventExpr>& clock, const std::string& parent_prefix,
    Arena& arena);

Expr* ProceduralActualInInstantiatingScope(
    Expr* actual, const std::string& parent_prefix,
    const std::vector<std::string_view>& locals, Arena& arena);

void SubstituteActualsInAssertion(Stmt& stmt, const ActualsByFormal& actuals,
                                  Arena& arena);

void CollectActualReadNames(Expr* actual, std::unordered_set<std::string>& out);

}  // namespace delta
