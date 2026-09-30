#pragma once

#include <string>
#include <unordered_set>

#include "common/arena.h"
#include "parser/ast_expr.h"

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

// §16.5.1 with §17.3: the names a sequence or property actual reads, which a
// checker's assertion reads sampled in the formal's place, added to `out`;
// nothing for any other actual.
void CollectActualReadNames(Expr* actual, std::unordered_set<std::string>& out);

}  // namespace delta
