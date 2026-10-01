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

// §17.3: the actual `actual` a checker instance binds to an event, sequence
// or property formal, as the checker's assertions read it in the formal's
// place: a copy whose every simple name stands in the scope instantiating
// the checker, `parent_prefix`, written from the top of the design, so that
// a name the checker declares too, its own formal among them, does not hide
// it. The locals of the actual's sequences are left as they are, and any
// other actual is answered as it is.
Expr* ActualInInstantiatingScope(Expr* actual, const std::string& parent_prefix,
                                 Arena& arena);

// §17.3 with §16.14.6.1: the actual `actual` a procedural checker instance
// binds to a formal, as the checker's assertions read it in the formal's
// place where it holds a const cast or reads one of `locals`, the variables
// the procedure declares around the instantiation: a copy whose other simple
// names stand in `parent_prefix`, as ActualInInstantiatingScope writes them,
// and whose locals are left bare, for their value to be saved when the
// instance is queued. nullptr for any other actual, which the formal's
// continuous assignment carries.
Expr* ProceduralActualInInstantiatingScope(
    Expr* actual, const std::string& parent_prefix,
    const std::vector<std::string_view>& locals, Arena& arena);

// §17.3: the copy `stmt` of a checker's assertion has each formal `actuals`
// names substituted by its actual in its property, its sequence, its
// expression and its disable condition, the trees it shares with the
// checker's own statement copied first.
void SubstituteActualsInAssertion(Stmt& stmt, const ActualsByFormal& actuals,
                                  Arena& arena);

// §16.5.1 with §17.3: the names a sequence or property actual reads, which a
// checker's assertion reads sampled in the formal's place, added to `out`;
// nothing for any other actual.
void CollectActualReadNames(Expr* actual, std::unordered_set<std::string>& out);

}  // namespace delta
