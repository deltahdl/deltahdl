#pragma once

#include <string>
#include <unordered_set>
#include <vector>

namespace delta {

// Forward declarations
struct Expr;
struct Stmt;
struct EventExpr;
class Arena;

/// Collect signal names read by an expression tree, using longest static
/// prefix (§11.5.3) for select expressions.
void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out);

/// Collect signal names read by a statement tree, using longest static
/// prefix (§11.5.3) for select expressions.
void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out);

/// Return the set of signal names read by a statement body.
std::vector<std::string> CollectReadSignals(const Stmt* body);

/// Infer a sensitivity list from read signals in a statement body.
/// Creates EventExpr nodes with Edge::kNone for each read signal.
std::vector<EventExpr> InferSensitivity(const Stmt* body, Arena& arena);

}  // namespace delta
