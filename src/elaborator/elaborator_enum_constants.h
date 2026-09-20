#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §6.19 declares an enumeration's literals as named constants of the scope
// holding the enumeration, §7.2 lets a structure or union member's type be
// any data_type, the enum form of Syntax 6-5 among them, and §23.9 lists no
// structure or union among the elements that define a scope, so an
// enumeration written as a member's type, at any depth, declares its literals
// where the outer type is written. Calls `fn` once for each enumeration `type`
// writes, in the order written: `type` itself when it is the enum form, and
// each member's inline type reached through StructMember::nested_type, which
// the parser fills for an inline enumeration, structure or union and leaves
// null for a member of a named type, which declares nothing here.
// `member_path` names the member the enumeration types, the member names from
// the outer type joined with '.', and is empty for `type` itself. Each
// enumeration numbers its own literals, so `enum_type` is what its values are
// folded from.
using EnumTypeVisitor = std::function<void(std::string_view member_path,
                                           const DataType& enum_type)>;
void ForEachEnumTypeIn(const DataType& type, const EnumTypeVisitor& fn);

// The enumerations one item declares, walked as ForEachEnumTypeIn walks them:
// Syntax 6-5 makes the enum form a data_type, so they stand in the type a
// typedef names or in the type of a data declaration. Other items declare
// none.
void ForEachEnumTypeOfItem(const ModuleItem* item, const EnumTypeVisitor& fn);

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

// §6.19.2 (Table 6-10): the names one enumeration member declares as
// constants of the enclosing scope. A member written as `name` declares that
// name; a `name[N]` or `name[N:M]` member declares the constants it
// generates, name0 through nameN-1 or nameN through nameM, and not the name
// it is written with. The bounds are folded against `scope`, and a member
// whose bound does not fold there -- one naming a parameter the scope does
// not hold -- is answered under its written name, so that a walk without the
// declaring scope's constants admits the member rather than dropping it. The
// names are owned by the answer, for a caller keeping them past any arena.
std::vector<std::string> EnumMemberDeclaredNames(const EnumMember& member,
                                                 const ScopeMap& scope);

// §6.19 makes an enumeration's members constants of the scope the enumeration
// is written in rather than of the type, and A.8.4 lists an enum identifier
// among the constant primaries, so an expression in that scope may read one
// wherever it may read a parameter. Binds each member of the enumeration
// `item` declares -- through a typedef, written directly as the data type of
// a data declaration, or written as the type of a structure or union member
// of either (ForEachEnumTypeOfItem) -- in `scope` under its name, folded
// against the constants already there, the enumerations before it in the same
// item included, and answers the members bound in the order declared. An item
// declaring no enumeration binds nothing and answers an empty list.
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
