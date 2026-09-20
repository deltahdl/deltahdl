#pragma once

#include <cstdint>
#include <optional>

#include "elaborator/const_eval.h"

namespace delta {

// §6.20.2 (printed page 127) with §6.12.1: the value of an integer parameter
// whose value expression `expr` is real -- has a real literal, a time literal
// or a call of one of §20.5's real-returning conversions as an operand --
// folded against `scope` and rounded to the nearest integer, ties away from
// zero. Empty for an expression with no real operand, whatever the integer
// fold made of it, and for a real value that is not a number, which §11.4.3
// (printed 276) leaves unspecified for a zero base raised to a negative
// power. Defined in elaborator_items_params.cpp, and read there by a
// parameter declared among a module's items and in elaborator_module.cpp by a
// parameter port.
std::optional<int64_t> FoldRealValueAsInteger(const Expr* expr,
                                              const ScopeMap& scope);

}  // namespace delta
