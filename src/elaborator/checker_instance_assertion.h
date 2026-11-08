#pragma once

#include <unordered_map>

#include "common/arena.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

namespace delta {

ModuleItem* CheckerInstanceAssertion(
    ModuleItem* item, const RtlirModule* mod,
    const std::unordered_map<const RtlirModule*, ActualsByFormal>& trees,
    const PropertyRegistry& registry, Arena& arena);

}  // namespace delta
