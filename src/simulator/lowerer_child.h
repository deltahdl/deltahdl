#ifndef DELTA_SIMULATOR_LOWERER_CHILD_H_
#define DELTA_SIMULATOR_LOWERER_CHILD_H_

#include <string>
#include <string_view>

#include "elaborator/rtlir_scopes.h"

namespace delta {

class SimContext;
struct RtlirModule;

// Defined in lowerer.cpp and shared with the child-module lowering split out
// into lowerer_child.cpp. RegisterInstanceKeyBinding records an instance's
// resolved library.cell for hierarchical name and %l/%L resolution.
// (A module's tasks and functions are published by RegisterModuleSubroutines
// and its let decls by RegisterModuleLets, both declared in
// lowerer_register.h.)
void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                const RtlirModule* mod, SimContext& ctx);

// §40.3.2.1 Table 40-2 with §23.6: the hierarchical path of the instance the
// run keys under `key`. The first top's declarations and instances are keyed
// with its name left off, which the path puts back; a later top's start with
// its own name already.
std::string CoverageScopeOfInstanceKey(const std::string& key,
                                       const SimContext& ctx);

// §27.5 with §23.9: the key the object a name written in a generate block
// stands for is held under, `name` being written under the instance
// `inst_prefix` names inside `gen_blocks`, outermost first. A generate block
// declares its objects under its prefix and a name declared locally stands
// over the enclosing scope's, so the innermost block declaring the name is the
// one meant, and the instance's own object where none does. A net is found
// with the rest, CreateNet registering its value as a variable of its name.
// §10.11's alias and §23.3.3's shared port connections read their names so.
std::string GenBlockObjectKey(const std::string& inst_prefix,
                              const GenBlockPrefixes& gen_blocks,
                              std::string_view name, SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_CHILD_H_
