#ifndef DELTA_ELABORATOR_COVERGROUP_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_RULES_H

#include <functional>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct CovergroupDecl;
struct ModuleDecl;
struct ModuleItem;

// The type of the variable a name a covergroup reads denotes, or nothing where
// it denotes none; and whether the name is visible where the covergroup is
// declared at all.
using CovergroupTypeOf =
    std::function<std::optional<DataTypeKind>(std::string_view)>;
using CovergroupDeclared = std::function<bool(std::string_view)>;

// The Clause 19 rules a covergroup is checked against once the declarations it
// reads are known, read from the tree the parser keeps for it
// (src/parser/ast_covergroup.h):
// - a coverpoint of a real expression declares at least one `bins` (§19.5),
//   its default bin is no array (§19.5.1), and its bins take no `with`
//   expression (§19.5.1.1);
// - a cross item is a coverpoint of its own covergroup or a variable, and no
//   real variable (§19.6).
void ValidateCovergroup(const CovergroupDecl& cg,
                        const CovergroupTypeOf& type_of,
                        const CovergroupDeclared& declared, DiagEngine& diag);

// The covergroups a module declares, checked by ValidateCovergroup, and the
// procedural writes through an instance of one to an option §19.7 restricts
// to the definition. `var_types` gives the type of each variable and net the
// module declares, and `declared` answers whether a name is visible in the
// module at all: its own declarations, its imports and its generate blocks.
void ValidateModuleCovergroups(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const CovergroupDeclared& declared, DiagEngine& diag);

// The covergroups embedded in `cls` (§19.4). A name such a covergroup reads is
// a property of the class or of a class it extends, or else an item of
// `scope_items`, the declarations of the scope the class is declared in.
void ValidateEmbeddedCovergroups(const ClassDecl* cls,
                                 const std::vector<ModuleItem*>& scope_items,
                                 const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_RULES_H
