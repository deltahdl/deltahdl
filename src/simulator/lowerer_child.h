#ifndef DELTA_SIMULATOR_LOWERER_CHILD_H_
#define DELTA_SIMULATOR_LOWERER_CHILD_H_

#include <string>
#include <string_view>

namespace delta {

struct RtlirModule;
class SimContext;

// Defined in lowerer.cpp and shared with the child-module lowering split out
// into lowerer_child.cpp. RegisterInstanceKeyBinding records an instance's
// resolved library.cell for hierarchical name and %l/%L resolution;
// RegisterModuleSubroutines publishes a module's tasks/functions and let decls.
void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                std::string_view library, std::string_view name,
                                SimContext& ctx);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_CHILD_H_
