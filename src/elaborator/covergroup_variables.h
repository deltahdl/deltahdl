#ifndef DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
#define DELTA_ELABORATOR_COVERGROUP_VARIABLES_H

#include <string_view>

#include "common/source_loc.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct CovergroupDecl;
struct RtlirModule;

// §19.3: the declaration of the covergroup a variable declared of type `dt`
// holds an instance of, read among the covergroups `mod` declares; null where
// `dt` names no covergroup of the module.
const CovergroupDecl* DeclaredCovergroup(const DataType& dt,
                                         const RtlirModule* mod);

// §19.3: a covergroup with a clocking event samples its instance at each
// occurrence of the event. Adds to `mod` an always process that waits on the
// event and calls sample() on the instance the variable `var_name` holds.
void AddCovergroupEventProcess(std::string_view var_name,
                               const CovergroupDecl& cg, SourceLoc loc,
                               RtlirModule* mod, Arena& arena);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_VARIABLES_H
