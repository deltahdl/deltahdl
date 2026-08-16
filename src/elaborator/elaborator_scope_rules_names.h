#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast.h"

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

// Collects the bare identifier reads of every procedural assignment's right
// side under `s`, dropping the ones `locals` names.
void CollectProcRhsIdents(const Stmt* s,
                          const std::unordered_set<std::string_view>& locals,
                          std::vector<const Expr*>& out);

// The names a subroutine's body may read without the module declaring them: its
// formal arguments, a function's own name, and what the body declares.
void CollectSubroutineLocalNames(const ModuleItem* item,
                                 std::unordered_set<std::string_view>& names);

}  // namespace delta
