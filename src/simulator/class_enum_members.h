#pragma once

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "parser/ast_class.h"
#include "simulator/class_object.h"
#include "simulator/sim_context.h"

namespace delta {

void CollectClassEnumMembers(ClassTypeInfo* info, const ClassDecl* cls,
                             const ScopeMap& scope, SimContext& ctx,
                             Arena& arena);

}  // namespace delta
