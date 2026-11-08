#pragma once

#include <vector>

namespace delta {

class Arena;
struct ElementDriveSource;
struct Expr;
class SimContext;
struct Stmt;
struct Variable;

std::vector<Variable*> CollectDistinctRhsVars(const Expr* rhs, SimContext& ctx,
                                              Variable* self);

bool TryContainerElementDrive(const Expr* lhs, const Stmt* stmt,
                              const ElementDriveSource& slot, SimContext& ctx,
                              Arena& arena);

}  // namespace delta
