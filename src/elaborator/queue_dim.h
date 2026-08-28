#pragma once

#include <cstdint>
#include <optional>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"

namespace delta {

struct Expr;
struct Stmt;

// §7.10, Syntax 7-4: a queue dimension is written `[$]` or `[$:N]`, and the
// parser records both as an identifier dimension whose text is "$", carrying
// the optional bound N on its rhs. Returns true when `dim` is one of those,
// whichever form, so that every site deciding whether a declaration declares a
// queue decides it the same way wherever the declaration stands.
bool IsQueueDim(const Expr* dim);

// §7.10: N in `[$:N]` is the highest index the queue may hold, and Syntax 7-4
// requires it to "evaluate to a positive integer value". Returns the number of
// elements that allows, which is one more than N, and returns nothing for a
// value the subclause rules out. The caller evaluates N itself, because a
// declaration among a module's items folds it against the parameter scope
// while one inside a procedural block evaluates it against the running
// process.
std::optional<int32_t> QueueBoundMaxSize(int64_t bound);

// §7.10: reports every queue bound written on a declaration inside the
// procedural block `s` that Syntax 7-4 rules out. A declaration inside a block
// never becomes an RtlirVariable, so nothing else evaluates its bound, and
// `[$:0]` would otherwise be accepted where the same bound at module scope is
// rejected. `scope` folds a parameter-valued bound, exactly as a module-scope
// declaration's does.
void CheckBlockQueueBounds(const Stmt* s, const ScopeMap& scope,
                           DiagEngine& diag);

}  // namespace delta
