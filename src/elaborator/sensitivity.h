#pragma once

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

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out);

void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out);

std::vector<std::string> CollectReadSignals(const Stmt* body);

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
