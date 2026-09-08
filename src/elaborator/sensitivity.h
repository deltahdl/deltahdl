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

}  // namespace delta
