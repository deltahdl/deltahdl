#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>

namespace delta {

// Forward declarations
struct Expr;

/// Map from identifier name to resolved constant value.
using ScopeMap = std::unordered_map<std::string_view, int64_t>;

/// Attempt to evaluate an expression as a constant integer.
/// Returns nullopt if the expression is not a compile-time constant.
std::optional<int64_t> ConstEvalInt(const Expr* expr);

/// Scoped overload: resolves identifiers via the given scope map.
std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope);

}  // namespace delta
