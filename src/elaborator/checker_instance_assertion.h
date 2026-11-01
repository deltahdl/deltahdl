#pragma once

#include <unordered_map>

#include "common/arena.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

namespace delta {

// §17.2 and §17.3: the assertion `item` of `mod` as the instance reads it.
// Where `mod` is a checker instance whose formals `trees` binds to sequences
// or properties, that is a copy, the item being shared by every instance of
// the checker, whose boolean, where it names such a formal, is the root of a
// tree the evaluator substitutes the actual into; `item` itself otherwise.
ModuleItem* CheckerInstanceAssertion(
    ModuleItem* item, const RtlirModule* mod,
    const std::unordered_map<const RtlirModule*, ActualsByFormal>& trees,
    const PropertyRegistry& registry, Arena& arena);

}  // namespace delta
