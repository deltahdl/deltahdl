#ifndef DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
#define DELTA_ELABORATOR_COVERGROUP_VARIABLES_H

namespace delta {

class Arena;
struct ModuleItem;
struct RtlirModule;
struct RtlirVariable;

// §19.3: records in `var` the declaration of the covergroup its type names,
// read among the covergroups `mod` declares. A covergroup with a clocking
// event samples its instance at each occurrence of the event, so for such a
// covergroup `mod` gains an always process that waits on the event and calls
// sample() on the instance the variable declared by `item` holds.
void BindCovergroupVariable(const ModuleItem& item, RtlirVariable& var,
                            RtlirModule* mod, Arena& arena);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
