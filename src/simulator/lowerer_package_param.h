#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct ModuleItem;
struct Variable;

uint32_t DeclaredParamStorageWidth(const ModuleItem* item, SimContext& ctx);

Logic4Vec HeldAtWidth(Logic4Vec value, uint32_t width, const Variable& var,
                      Arena& arena);

void InitPackageParam(const ModuleItem* item, Variable* var, SimContext& ctx,
                      Arena& arena);

}  // namespace delta
