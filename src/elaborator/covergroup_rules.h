#ifndef DELTA_ELABORATOR_COVERGROUP_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_RULES_H

#include <functional>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/coverpoint_bin_set_expression.h"
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

// The arrays a covergroup reads where it is declared: the kind of array a name
// denotes, or nothing where it denotes no unpacked array, and whether a name is
// a type, as the index of an associative array may be (§7.8).
struct CovergroupArrays {
  std::function<std::optional<SetExpressionArrayKind>(std::string_view)>
      kind_of;
  CovergroupDeclared is_type;
};

// The Clause 19 rules a covergroup is checked against once the declarations it
// reads are known, read from the tree the parser keeps for it
// (src/parser/ast_covergroup.h):
// - a coverpoint of a real expression declares at least one `bins` (§19.5),
//   its default bin is no array (§19.5.1), and its bins take no `with`
//   expression (§19.5.1.1);
// - a coverpoint of a real expression has no transition bin (§19.5.2);
// - a bin's set_covergroup_expression yields no associative array, nor one
//   whose elements are not assignment compatible with the coverpoint's type,
//   and reads no name declared only within the covergroup (§19.5.1.2),
//   `arrays` giving the kind of array a name denotes;
// - a cross item is a coverpoint of its own covergroup or a variable, and no
//   real variable (§19.6).
void ValidateCovergroup(const CovergroupDecl& cg,
                        const CovergroupTypeOf& type_of,
                        const CovergroupDeclared& declared,
                        const CovergroupArrays& arrays, DiagEngine& diag);

// The covergroups a module declares, checked by ValidateCovergroup and for a
// set_covergroup_expression reading a name the module does not declare
// (§23.9), and the procedural writes through an instance of one to an option
// §19.7 restricts to the definition. `var_types` gives the type of each
// variable and net the module declares, and `declared` answers whether a name
// is visible in the module at all: its own declarations, its imports and its
// generate blocks.
void ValidateModuleCovergroups(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const CovergroupDeclared& declared, DiagEngine& diag);

// Whether a bare name denotes a covergroup type where a module reads it.
using CovergroupTypeVisible = std::function<bool(std::string_view)>;

// §19.8: get_coverage() is the one covergroup method called through the
// covergroup type, `cg::get_coverage()` or `cg::x::get_coverage()`; a call
// through a type `visible` names to any other method, in a procedure or a
// subroutine of `decl`, is reported. So is a procedural write there through
// such a type to the strobe or real_interval type option, which §19.7.1 lets
// the covergroup definition alone set.
void ValidateCovergroupTypeCalls(const ModuleDecl* decl,
                                 const CovergroupTypeVisible& visible,
                                 DiagEngine& diag);

// The covergroups embedded in `cls` (§19.4). A name such a covergroup reads is
// a property of the class or of a class it extends, or else an item of
// `scope_items`, the declarations of the scope the class is declared in; a
// name a set_covergroup_expression reads that `unit_declared` denies any
// declaration of the unit gives is unresolved (§23.9).
void ValidateEmbeddedCovergroups(const ClassDecl* cls,
                                 const std::vector<ModuleItem*>& scope_items,
                                 const CompilationUnit* unit,
                                 const CovergroupDeclared& unit_declared,
                                 DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_RULES_H
