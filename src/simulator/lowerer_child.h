#ifndef DELTA_SIMULATOR_LOWERER_CHILD_H_
#define DELTA_SIMULATOR_LOWERER_CHILD_H_

#include <string>
#include <string_view>

#include "elaborator/rtlir_scopes.h"

namespace delta {

class SimContext;
struct Expr;
struct Net;
struct RtlirModule;

void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                const RtlirModule* mod, SimContext& ctx);

void RegisterTypeRefCompares(const std::string& inst_prefix,
                             const RtlirModule* mod, SimContext& ctx);

std::string CoverageScopeOfInstanceKey(const std::string& key,
                                       const SimContext& ctx);

std::string GenBlockObjectKey(const std::string& inst_prefix,
                              const GenBlockPrefixes& gen_blocks,
                              std::string_view name, SimContext& ctx);

void JoinInoutPortBits(const Expr& connection, Net& port_net,
                       const std::string& inst_prefix,
                       const GenBlockPrefixes& gen_blocks, SimContext& ctx);

}  // namespace delta

#endif
