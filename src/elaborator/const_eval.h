#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

namespace delta {

struct Expr;

using ScopeMap = std::unordered_map<std::string_view, int64_t>;

std::optional<int64_t> ConstEvalInt(const Expr* expr);

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope);

std::optional<double> ConstEvalReal(const Expr* expr);
std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope);

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope = {});

// Shared with §13.4.3: the whitelist of system functions admissible inside a
// constant_expression (§11.2.1) is the same set that a constant function may
// invoke per §13.4.3 constraint (g).
bool IsConstantSysFunc(std::string_view name);

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope = {});

}  // namespace delta
