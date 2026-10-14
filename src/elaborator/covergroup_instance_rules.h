#ifndef DELTA_ELABORATOR_COVERGROUP_INSTANCE_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_INSTANCE_RULES_H

#include "elaborator/covergroup_context.h"

namespace delta {

class DiagEngine;
struct CovergroupDecl;
struct Expr;
struct ModuleDecl;

// §19.3: the actuals the call `call` of `new` gives an instance of `cg` bind
// to its formals as §13.5 binds a subroutine's: each formal without a default
// is given one, each actual binds a formal, and the actual of a `ref` formal
// is a variable, no net `is_net` names.
void CheckCovergroupNewActuals(const Expr* call, const CovergroupDecl& cg,
                               const CovergroupDeclared& is_net,
                               DiagEngine& diag);

// The rules on the instances of the covergroups the module `decl` declares, in
// its declarations, procedures and subroutines:
// - each `new` building one obeys CheckCovergroupNewActuals (§19.3);
// - no formal of the covergroup is read through an instance, its formals being
//   visible within the declaration alone (§19.3);
// - sample() and set_inst_name() are called on the instance, never on one of
//   its coverpoints or crosses (§19.8, Table 19-5).
void CheckModuleCovergroupInstances(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_INSTANCE_RULES_H
