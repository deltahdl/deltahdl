#pragma once

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "parser/ast.h"

// Internal helpers shared between the translation units that elaborate module
// instantiations (elaborator_module_inst.cpp) and the other elaborator
// translation units that instantiate a module through a different syntactic
// form. These are not part of the public elaborator interface.
namespace delta {

// Resolves an instantiation's own parameter overrides (named or positional)
// against the child module's overridable parameters, evaluating each override
// expression in `parent_scope` and appending the results to `child_params`.
// Defined in elaborator_module_inst.cpp.
void ResolveInstParams(const ModuleItem* item, const ModuleDecl* child_decl,
                       const ScopeMap& parent_scope,
                       Elaborator::ParamList& child_params, DiagEngine& diag);

}  // namespace delta
