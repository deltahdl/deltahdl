#pragma once

#include <cstdint>
#include <optional>
#include <string>
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

/// §11.5.3: Compute the longest static prefix of a select expression.
/// Returns a string representation (e.g., "m[1]" for m[1][i]).
/// The scope map is used to determine which identifiers are constants.
std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope = {});

}  // namespace delta
