#ifndef DELTA_SIMULATOR_BLOCK_ENUMS_H_
#define DELTA_SIMULATOR_BLOCK_ENUMS_H_

#include <functional>

#include "parser/ast_stmt.h"
#include "simulator/sim_context_types.h"

namespace delta {

class Arena;
struct RtlirDesign;
struct RtlirModule;
class SimContext;

void RegisterBlockEnumTypes(const RtlirModule* mod, const RtlirDesign* design,
                            SimContext& ctx, Arena& arena);

void ForEachBlockEnumMember(
    const Stmt* stmt, SimContext& ctx,
    const std::function<void(const EnumMemberInfo&, const EnumTypeInfo&)>& fn);

}  // namespace delta

#endif
