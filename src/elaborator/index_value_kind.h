#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>

#include "parser/ast_type.h"

namespace delta {

struct Expr;

// The kinds of value §7.8.1 to §7.8.4 tell an associative index by.
enum class IndexValueKind : uint8_t { kUnknown, kIntegral, kReal, kString };

// §7.8.1 to §7.8.4 (printed pages 163–164): the kind of value the index
// expression `e` gives, as far as its form and the declared kinds `var_types`
// of the variables it names tell: a numeric literal by its own kind, a
// variable real or integral by its declared kind, an arithmetic operator real
// when either operand is and integral otherwise, any other operator integral,
// a unary operator its operand's kind, and a string method by the result
// §6.16 gives it. Anything else is kUnknown. A literal or a variable written
// alone as the index is judged by its caller, which knows the rule at hand.
IndexValueKind KindOfIndexValue(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types);

}  // namespace delta
