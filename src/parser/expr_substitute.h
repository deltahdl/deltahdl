#pragma once

#include <string_view>
#include <unordered_map>

#include "common/arena.h"
#include "parser/ast_expr.h"

namespace delta {

// An expression to stand for each name, the actual argument bound to a formal
// in §16.8's and §16.12's instantiation of a named sequence or property.
using ActualsByFormal = std::unordered_map<std::string_view, Expr*>;

// §F.4.1's rewriting: a copy of `e` in which every identifier the map names
// is replaced by the expression mapped to it, the rest copied node by node;
// nullptr for nullptr. The copy shares nothing with `e` but the leaves the
// map supplies.
Expr* SubstituteFormals(const Expr* e, const ActualsByFormal& actuals,
                        Arena& arena);

}  // namespace delta
