#ifndef DELTA_SIMULATOR_LOWERER_CHILD_H_
#define DELTA_SIMULATOR_LOWERER_CHILD_H_

#include <string>
#include <string_view>

namespace delta {

class SimContext;

// Defined in lowerer.cpp and shared with the child-module lowering split out
// into lowerer_child.cpp. RegisterInstanceKeyBinding records an instance's
// resolved library.cell for hierarchical name and %l/%L resolution.
// (A module's tasks, functions and let decls are published by
// RegisterModuleSubroutines, declared in lowerer_register.h.)
void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                std::string_view library, std::string_view name,
                                SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_CHILD_H_
