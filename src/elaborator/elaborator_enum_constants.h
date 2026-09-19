#pragma once

#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §6.19: the named constants an enumeration declares, in declaration order,
// each with the value it stands for. A member written with a value takes it,
// one written without takes the previous member's value plus one, the first
// starting from 0, and a `name[N]` or `name[N:M]` member expands to one
// constant per index (§6.19.2, Table 6-10). A value or range bound is a
// constant expression folded against `scope`, which is where the parameters,
// local parameters and other enumeration constants the clause lets it name are
// read from. `arena` owns the names the range forms generate.
std::vector<RtlirEnumMember> FoldEnumMembers(
    const std::vector<EnumMember>& decl_members, const ScopeMap& scope,
    Arena& arena);

// §6.19 makes an enumeration's members constants of the scope the enumeration
// is written in rather than of the type, and A.8.4 lists an enum identifier
// among the constant primaries, so an expression in that scope may read one
// wherever it may read a parameter. Binds each member of the enumeration
// `item` declares -- through a typedef, or written directly as the data type
// of a data declaration -- in `scope` under its name, folded against the
// constants already there, and answers the members bound. An item declaring
// no enumeration binds nothing and answers an empty list.
std::vector<RtlirEnumMember> BindEnumConstantsOfItem(const ModuleItem* item,
                                                     ScopeMap& scope,
                                                     Arena& arena);

}  // namespace delta
