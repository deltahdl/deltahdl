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

// §40.3.2.1 Table 40-2 with §23.6: the hierarchical path of the instance the
// run keys under `key`. The first top's declarations and instances are keyed
// with its name left off, which the path puts back; a later top's start with
// its own name already.
std::string CoverageScopeOfInstanceKey(const std::string& key,
                                       const SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_CHILD_H_
