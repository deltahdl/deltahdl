#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"

namespace delta {

struct ModuleDecl;

// §6.20.7 (printed page 131): a parameter to which `$` is assigned may stand
// wherever `$` may be written as a literal, except in a queue context. Reports
// each such parameter, of the names in `unbounded`, that the module `decl`
// writes as a queue's dimension, `int q[P]`, or inside a queue dimension's
// bound, `int q[$:P]`, and each written inside an index or a slice of one of
// the queue variables `queues` names, `q[P]` or `q[0:P-1]`.
void CheckUnboundedParamsInQueueContexts(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& unbounded,
    const std::unordered_set<std::string_view>& queues, DiagEngine& diag);

// §6.20.7 (printed pages 130-131): `$` may be written only in the contexts the
// subclause lists, and as an entire expression everywhere but a queue select.
// Reports each `$` the module `decl` writes as an operand, or as the whole
// value, of an assignment, a continuous assignment, a declaration's
// initializer, a condition or an expression statement. A select's index and a
// value range's bounds are left alone, a queue select and a value range being
// contexts the subclause lists, as are a call's arguments, which may be a
// sequence's, a property's or a checker's actual arguments, and an assertion's
// expression, which holds the cycle delay ranges.
void CheckDollarOperands(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
