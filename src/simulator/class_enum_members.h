#pragma once

#include "common/arena.h"
#include "parser/ast_class.h"
#include "simulator/class_object.h"
#include "simulator/sim_context.h"

namespace delta {

// §8.23 with §6.19: binds in `info` the literals of every enumeration the
// class `cls` declares, by a typedef or inline on a property, and registers
// each enumeration with `ctx`.
void CollectClassEnumMembers(ClassTypeInfo* info, const ClassDecl* cls,
                             SimContext& ctx, Arena& arena);

}  // namespace delta
