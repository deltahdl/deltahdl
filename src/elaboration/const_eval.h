#pragma once

#include <cstdint>
#include <optional>

namespace delta {

// Forward declarations
struct Expr;

/// Attempt to evaluate an expression as a constant integer.
/// Returns nullopt if the expression is not a compile-time constant.
std::optional<int64_t> ConstEvalInt(const Expr* expr);

}  // namespace delta
