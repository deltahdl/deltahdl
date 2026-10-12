#pragma once

#include <functional>
#include <span>
#include <string_view>

#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct Expr;

// The kind of type an operand `operand` is known to have where it names a
// variable or calls a function of the scope; DataTypeKind::kImplicit where the
// scope does not tell it.
using OperandKind = std::function<DataTypeKind(const Expr& operand)>;

// Reports the member access `access`, a method call's callee `(x + 1).run` or
// a member select `{a, b}.m`, naming nothing the value its left-hand side
// yields has:
// - §11.8.1: a unary, binary, increment or decrement, or `inside` operator
//   yields an integral or a real value, which has no member and no built-in
//   method. A parenthesized `=` is no such operator: §11.3.6 gives it the value
//   it assigns, of its left-hand side's type.
// - §11.4.12.2: a concatenation or a multiple concatenation with an operand of
//   the string type, as `operand_kind` tells it, is a string, whose built-in
//   methods are `string_methods` (§6.16).
// - §11.4.12: any other concatenation is a vector of bits, which has no member
//   and no built-in method, where the type of each of its operands is known.
// Defined in operator_result_members.cpp.
void ReportOperatorResultMember(
    const Expr& access, const OperandKind& operand_kind,
    std::span<const std::string_view> string_methods, DiagEngine& diag);

}  // namespace delta
