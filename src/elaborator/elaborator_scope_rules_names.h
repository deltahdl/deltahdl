#pragma once

#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// The names a §23.9 unresolved-reference check has to know about before it can
// call a bare identifier unresolved, and the reads it has to find.
//
// §23.9 rules that an identifier referenced without a hierarchical path is
// searched for upward and that the search "shall stop at a module boundary"
// when the item is a variable, so a name no scope the reference can reach
// declares is an error. What makes the check hard is not the rule but the names
// a module declares elsewhere than in its own symbol table: §23.9 lists a
// generate block among the elements that define a scope, §26.3 makes every name
// a wildcard-imported package declares directly visible, and §13.3 makes a
// subroutine's formal arguments declarations of the subroutine. Each collector
// here answers one of those, so the check consults a set of names rather than
// giving up on the module that holds one.
//
// Every collector over-approximates deliberately. A name in the set can only
// suppress a diagnostic and never raise one, so a scope boundary a walk does
// not track is always safe.

// Collects the standalone identifier operands of `e` that a value read could
// name. A member-access subtree is not descended into, so the base of `a.b`,
// `s.field`, `$root.x` and `pkg::x`, and anything under a `with` clause hanging
// off one, is never collected; a scope-prefixed identifier, a builtin type
// keyword, `null` and `$` are skipped for the same reason. What survives is the
// plain reads that must resolve to a declaration.
void CollectBareIdents(const Expr* e, std::vector<const Expr*>& out);

// The hash a ProvidedNames map is keyed by. It hashes a std::string_view and
// is transparent, so the map is looked up with the string_view a reference
// carries without a std::string being built for each lookup.
struct ProvidedNameHash {
  // The name the standard library looks for on a transparent hash.
  using is_transparent = void;
  size_t operator()(std::string_view name) const noexcept {
    return std::hash<std::string_view>{}(name);
  }
};

// The names a package makes directly visible, each with the name of the
// package that declares it: the package itself for its own declarations, and
// the package at the end of the export chain for a name an export hands on.
// §26.6 makes an import of a declaration reached through an export an import of
// the original declaration, so two wildcard imports supplying one name are one
// candidate where the declaring packages agree and §26.3's conflict where they
// differ. The map owns its keys: the constants a `name[N]` member of §6.19.2
// generates are spelled by no declaration, so a key is a std::string rather
// than a view into the syntax tree, and the origin, a package's name, stays a
// view of the declaration.
using ProvidedNames = std::unordered_map<std::string, std::string_view,
                                         ProvidedNameHash, std::equal_to<>>;

// The names the package `pkg_name` makes directly visible to a scope that
// imports it by wildcard: every declaration of its own, with the constants of
// each enumeration it declares (§26.5), a ranged member of §6.19.2 by the
// names it generates, and what its export declarations hand on of what it
// imports (§26.6); a name it imports without exporting is not among them.
// Nothing is added for a package the unit does not declare.
void PopulatePackageProvidedNames(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  ProvidedNames& names);

// The names each package makes directly visible, each with the package that
// declares it, filled on first use by ProvidedNameOrigin;
// Elaborator::pkg_provided_names_ is one.
using ProvidedNameCache = std::unordered_map<std::string_view, ProvidedNames>;

// Whether the unit declares the package `pkg_name`; §26.7's built-in package
// std is always declared.
bool PackageDeclared(const CompilationUnit* unit, std::string_view pkg_name);

// The package declaring `name` as the wildcard-imported package `pkg_name`
// provides it, or empty where `pkg_name` does not provide the name.
std::string_view ProvidedNameOrigin(const CompilationUnit* unit,
                                    ProvidedNameCache& provided_cache,
                                    std::string_view pkg_name,
                                    std::string_view name);

// Whether the wildcard-imported package `pkg_name` provides `name`.
bool PackageProvidesName(const CompilationUnit* unit,
                         ProvidedNameCache& provided_cache,
                         std::string_view pkg_name, std::string_view name);

// The packages a module imports by wildcard, whose declarations §26.3 makes
// directly visible to a bare read.
std::vector<std::string_view> WildcardImportedPackages(const RtlirModule* mod);

// The names a module's generate constructs and its genvars declare.
void CollectModuleGenerateNames(const std::vector<ModuleItem*>& items,
                                std::unordered_set<std::string_view>& names);

// The names a procedural block declares: a block variable declaration, a
// for-loop control variable and a foreach index variable.
void CollectProcLocalNames(const Stmt* s,
                           std::unordered_set<std::string_view>& names);

// Collects the bare identifier reads under `s`: every procedural assignment's
// right side, every argument of a display, write, strobe, monitor or severity
// system task statement, every statement's condition, for condition and case
// item pattern (a `matches` case's aside), and every expression a randsequence
// statement holds outside its code blocks, dropping the ones `locals` names.
void CollectProcRhsIdents(const Stmt* s,
                          const std::unordered_set<std::string_view>& locals,
                          std::vector<const Expr*>& out);

// The names a subroutine's body may read without the module declaring them: its
// formal arguments, a function's own name, and what the body declares.
void CollectSubroutineLocalNames(const ModuleItem* item,
                                 std::unordered_set<std::string_view>& names);

// The name sets of the compilation-unit scope (§3.12.1) a read resolves
// against where no module's own names apply, as
// Elaborator::RegisterCuScopeItems fills them: the unit's item names
// (cu_scope_names_), its constants (cu_param_scope_), its typedefs (typedefs_)
// and its classes (class_names_).
struct UnitScopeNames {
  const std::unordered_set<std::string_view>& item_names;
  const ScopeMap& constants;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

// §23.9 over the subroutines the compilation unit and each package declare,
// which no module's walk reaches; reports every bare read that none of `names`,
// the scope's own declarations and imports, or the body's own names answers.
void ReportUnresolvedInUnitScopeSubroutines(const CompilationUnit* unit,
                                            const UnitScopeNames& names,
                                            ProvidedNameCache& provided_cache,
                                            DiagEngine& diag);

}  // namespace delta
