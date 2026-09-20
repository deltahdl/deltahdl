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

// §26.3 with §6.20.1: an import written in a package makes another package's
// parameters and enumeration constants visible in the package by their bare
// names, so a declaration after it reads one as a constant expression --
// `import base::K; parameter int KK = K;`. Binds in `scope` what the import
// item `imp` of `pkg` brings in, read from `cu_param_scope` under the
// "package.name" keys the imported package's constants were recorded under
// (RegisterPackageParams in elaborator_resolve.cpp): the one name of an
// explicit import, or every constant of the package for a wildcard. §26.5's
// Table 26-1 has a declaration of the importing scope win over a wildcard's
// candidate of the same name, so a wildcard leaves alone the names `pkg`
// declared ahead of the import. An item that is no import binds nothing.
void BindPackageImportConstants(const PackageDecl* pkg, const ModuleItem* imp,
                                const ScopeMap& cu_param_scope,
                                ScopeMap& scope);

}  // namespace delta
