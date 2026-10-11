#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace delta {

struct Expr;
struct Stmt;
struct EventExpr;
struct ModuleItem;
struct ModuleDecl;
struct ClassDecl;
class Arena;

using FuncMap = std::unordered_map<std::string_view, const ModuleItem*>;

void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out);

// The expressions a statement reads, in the positions §9.2.2.2.1's inferred
// sensitivity list takes them from, handed over one at a time. CollectStmtReads
// below is this walk with the names collected off each expression, and a caller
// that needs the expressions themselves asks this instead of restating the
// positions: §25.9's ban on a virtual interface component in a sensitivity list
// is one, `vif.a` having become the two bare identifiers `vif` and `a` by the
// time the names exist, and a check that walked more positions than the
// inference does would reject a component the list never carries.
//
// `fn` is called with a null expression where a position is absent, so a caller
// that reads the expression handles null as CollectExprReads does.
void ForEachStmtReadExpr(const Stmt* stmt,
                         const std::function<void(const Expr*)>& fn);

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out);

void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out);

// §9.2.2.2.1: the implicit sensitivity list expands the longest static prefix
// of each *net or variable* identifier or select expression read by the
// process. `const_names`, when supplied, names the identifiers that are
// elaboration-time constants (parameters, localparams, specparams) rather than
// nets or variables; a read of such a name -- whether a direct operand or a
// constant select index -- is excluded from the list, since a constant can
// never change to trigger the process.
std::vector<EventExpr> InferSensitivity(
    const Stmt* body, Arena& arena, const FuncMap* funcs = nullptr,
    bool exclude_written = true,
    const std::unordered_set<std::string_view>* const_names = nullptr);

// §9.2.2.2.1 with §8.23 and §23.6: `funcs` and, besides, the functions an
// always_comb in a module holding `items` may call by a scoped name, each under
// the key its call spells: every static function of a class `items` or the
// compilation unit (`unit_classes`) declares under "C::f", and every function
// of the module `find_module` finds for an instance `items` declares under
// "s.f", the instance's name. Only the inference reads the result; the
// elaborator's own function table stays as it is for every other rule.
FuncMap WithScopedCallFunctions(
    const FuncMap& funcs, const std::vector<ModuleItem*>& items,
    const std::vector<ClassDecl*>& unit_classes,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    Arena& arena);

}  // namespace delta
