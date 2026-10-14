#ifndef DELTA_ELABORATOR_COVERGROUP_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_RULES_H

#include <functional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/covergroup_context.h"
#include "elaborator/value_kind.h"

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct CovergroupDecl;
struct ModuleDecl;
struct ModuleItem;

// The Clause 19 rules a covergroup is checked against once the declarations it
// reads are known, read from the tree the parser keeps for it
// (src/parser/ast_covergroup.h), `ctx` answering for those declarations:
// - a coverpoint of a real expression declares at least one `bins` (§19.5),
//   its default bin is no array (§19.5.1), and its bins take no `with`
//   expression (§19.5.1.1), no transition (§19.5.2) and no `wildcard`
//   (§19.5.4);
// - every coverpoint obeys CheckCoverpointRules (§19.5 to §19.5.1.1);
// - its covergroup_expressions obey CheckCovergroupExpressions (§19.5, §19.6);
// - a bin's set_covergroup_expression yields no associative array, nor one
//   whose elements are not assignment compatible with the coverpoint's type,
//   and reads no name declared only within the covergroup (§19.5.1.2);
// - a cross item is a coverpoint of its own covergroup or a variable, and no
//   real variable (§19.6), and the cross's bins obey CheckCrossBinRules
//   (§19.6.1.2, §19.6.1.4);
// - its coverage options obey CheckCoverageOptions (§19.7, §19.7.1, §19.10).
void ValidateCovergroup(const CovergroupDecl& cg, const CovergroupContext& ctx,
                        DiagEngine& diag);

// The tables of a module its covergroups read (§19.3): the declarations
// `values` holds, and the names `const_names` holds of its parameters and
// const variables, the constants among them.
struct ModuleCovergroupTables {
  const ValueScope& values;
  const std::unordered_set<std::string_view>& const_names;
};

// The covergroups a module declares, checked by ValidateCovergroup and for a
// set_covergroup_expression reading a name the module does not declare
// (§23.9); their instances, by CheckModuleCovergroupInstances (§19.3, §19.8);
// and the procedural writes through an instance of one to an option §19.7
// restricts to the definition or §19.10 does not declare. `declared` answers
// whether a name is visible in the module at all: its own declarations, its
// imports and its generate blocks.
void ValidateModuleCovergroups(const ModuleDecl* decl,
                               const ModuleCovergroupTables& tables,
                               const CovergroupDeclared& declared,
                               DiagEngine& diag);

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
// declaration of the unit gives is unresolved (§23.9); and the class around
// them is held to CheckEmbeddedCovergroupUses.
void ValidateEmbeddedCovergroups(const ClassDecl* cls,
                                 const std::vector<ModuleItem*>& scope_items,
                                 const CompilationUnit* unit,
                                 const CovergroupDeclared& unit_declared,
                                 DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_RULES_H
