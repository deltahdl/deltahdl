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

// §6.19 with A.2.8: a begin-end block, a fork-join block or a subroutine body
// may declare a typedef among its items, and the enumeration it declares is
// a type of that block, its members named constants of the block (§23.9).
//
// Registers each enumeration a block of `mod`'s procedures and subroutines
// declares so, under a key of its own typedef that no other block's shares,
// so that two blocks declaring `typedef enum {p, q} e_t;` over different
// bases keep apart. Each variable declaration the block's statements make
// with the typedef's name, after the typedef, is reshaped to name that key
// (SimContext::ClassTypedefShapedDecls, read by DeclShapedByTypedef), so the
// variable is of the block's enumeration, as wide and as signed as it.
// Member values fold against the compilation unit's constants, `mod`'s
// parameters and its enumeration constants.
void RegisterBlockEnumTypes(const RtlirModule* mod, const RtlirDesign* design,
                            SimContext& ctx, Arena& arena);

// Calls `fn` for each member of each enumeration the block item declaration
// `stmt` declares, with the enumeration it belongs to, as
// RegisterBlockEnumTypes registered it; a statement declaring none calls
// nothing. The caller declares each member as a constant of the running
// block.
void ForEachBlockEnumMember(
    const Stmt* stmt, SimContext& ctx,
    const std::function<void(const EnumMemberInfo&, const EnumTypeInfo&)>& fn);

}  // namespace delta

#endif  // DELTA_SIMULATOR_BLOCK_ENUMS_H_
