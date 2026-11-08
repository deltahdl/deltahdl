#pragma once

#include <functional>
#include <span>
#include <string_view>

#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct Expr;

using OperandKind = std::function<DataTypeKind(const Expr& operand)>;

void ReportOperatorResultMember(
    const Expr& access, const OperandKind& operand_kind,
    std::span<const std::string_view> string_methods, DiagEngine& diag);

}  // namespace delta
