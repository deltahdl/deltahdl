#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace delta {

// Forward declarations
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

std::vector<EventExpr> InferSensitivity(const Stmt* body, Arena& arena,
                                        const FuncMap* funcs = nullptr);

}  // namespace delta
