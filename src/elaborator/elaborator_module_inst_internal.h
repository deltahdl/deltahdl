#pragma once

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "parser/ast_module.h"

namespace delta {

void ResolveInstParams(const ModuleItem* item, const ModuleDecl* child_decl,
                       const ScopeMap& parent_scope,
                       Elaborator::ParamList& child_params, DiagEngine& diag);

}  // namespace delta
