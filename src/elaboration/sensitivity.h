#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

// Forward declarations
struct Expr;
struct Stmt;
struct EventExpr;
class Arena;

/// Collect all identifier names read by an expression tree.
void CollectExprReads(const Expr* expr,
                      std::unordered_set<std::string_view>& out);

/// Collect all identifier names read by a statement tree.
void CollectStmtReads(const Stmt* stmt,
                      std::unordered_set<std::string_view>& out);

/// Return the set of signal names read by a statement body.
std::vector<std::string_view> CollectReadSignals(const Stmt* body);

/// Infer a sensitivity list from read signals in a statement body.
/// Creates EventExpr nodes with Edge::kNone for each read signal.
std::vector<EventExpr> InferSensitivity(const Stmt* body, Arena& arena);

}  // namespace delta
