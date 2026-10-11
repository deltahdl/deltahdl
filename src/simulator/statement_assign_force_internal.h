#pragma once

#include <vector>

namespace delta {

class Arena;
struct ElementDriveSource;
struct Expr;
class SimContext;
struct Stmt;
struct Variable;

// §10.6: the distinct variables `rhs` reads, `self` left out, which a
// procedural continuous assignment's right-hand side is recomputed on a change
// of. Defined in statement_assign_force_element.cpp; also used by the
// statements on a variable or a net in statement_assign_force.cpp.
std::vector<Variable*> CollectDistinctRhsVars(const Expr* rhs, SimContext& ctx,
                                              Variable* self);

// §10.6.1 and §10.6.2 on an element of a queue or an associative array, which
// has no Variable of its own: answers one of the four statements on the
// element `lhs` names, and whether it names one. `slot` is the concatenation
// slot the element takes, zero-wide for a lone target. Defined in
// statement_assign_force_element.cpp.
bool TryContainerElementDrive(const Expr* lhs, const Stmt* stmt,
                              const ElementDriveSource& slot, SimContext& ctx,
                              Arena& arena);

}  // namespace delta
