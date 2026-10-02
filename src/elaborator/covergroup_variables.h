#ifndef DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
#define DELTA_ELABORATOR_COVERGROUP_VARIABLES_H

#include <string_view>

namespace delta {

class Arena;
struct CompilationUnit;
struct CovergroupDecl;
struct ModuleItem;
struct RtlirModule;
struct RtlirVariable;

// The covergroup the bare name `name` denotes in `mod`, or null where it
// denotes none: one `mod` declares, else, by §26.3, one of a package that an
// import `mod` has reached by now makes visible, else one the compilation unit
// `unit` declares (§3.12.1).
const CovergroupDecl* VisibleCovergroup(std::string_view name,
                                        const RtlirModule* mod,
                                        const CompilationUnit* unit);

// §19.3: records in `var` the declaration of the covergroup its type names,
// read among the covergroups `mod` declares and, by §26.3, those of the
// packages of `unit` that the type's package scope or `mod`'s imports name.
// A covergroup with a clocking event samples its instance at each occurrence
// of the event, so for such a covergroup `mod` gains an always process that
// waits on the event and calls sample() on the instance the variable declared
// by `item` holds.
void BindCovergroupVariable(const ModuleItem& item, RtlirVariable& var,
                            RtlirModule* mod, const CompilationUnit* unit,
                            Arena& arena);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
