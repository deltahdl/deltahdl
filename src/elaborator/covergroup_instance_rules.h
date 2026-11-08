#ifndef DELTA_ELABORATOR_COVERGROUP_INSTANCE_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_INSTANCE_RULES_H

#include "elaborator/covergroup_context.h"

namespace delta {

class DiagEngine;
struct CovergroupDecl;
struct Expr;
struct ModuleDecl;

void CheckCovergroupNewActuals(const Expr* call, const CovergroupDecl& cg,
                               const CovergroupDeclared& is_net,
                               DiagEngine& diag);

void CheckModuleCovergroupInstances(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta

#endif
