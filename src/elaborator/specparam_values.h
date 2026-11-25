#pragma once

#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

class Arena;
struct ModuleItem;
struct RtlirModule;

void RecordSpecparams(const std::vector<ModuleItem*>& items, RtlirModule& mod,
                      Arena& arena);

void ResolveSpecparams(RtlirModule& mod, ScopeMap scope,
                       const TypedefMap& typedefs);

}  // namespace delta
