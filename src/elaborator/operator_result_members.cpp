#include "elaborator/operator_result_members.h"

#include <algorithm>
#include <cstdint>
#include <format>
#include <span>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

enum class ResultValue : std::uint8_t { kUnknown, kNumber, kBits, kString };

}  // namespace

static ResultValue ConcatenationValue(const Expr& e,
                                      const OperandKind& operand_kind) {
  ResultValue value = ResultValue::kBits;
  for (const Expr* operand : e.elements) {
    if (operand->kind == ExprKind::kIntegerLiteral ||
        operand->kind == ExprKind::kStringLiteral)
      continue;
    const DataTypeKind kKind = operand_kind(*operand);
    if (kKind == DataTypeKind::kString) return ResultValue::kString;
    if (kKind == DataTypeKind::kImplicit) value = ResultValue::kUnknown;
  }
  return value;
}

static ResultValue ResultValueOf(const Expr& e,
                                 const OperandKind& operand_kind) {
  switch (e.kind) {
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
    case ExprKind::kInside:
      return ResultValue::kNumber;
    case ExprKind::kBinary:
      return e.op == TokenKind::kEq ? ResultValue::kUnknown
                                    : ResultValue::kNumber;
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return ConcatenationValue(e, operand_kind);
    default:
      return ResultValue::kUnknown;
  }
}

void ReportOperatorResultMember(
    const Expr& access, const OperandKind& operand_kind,
    std::span<const std::string_view> string_methods, DiagEngine& diag) {
  const std::string_view kName = access.rhs->text;
  const SourceLoc kLoc = access.rhs->range.start;
  switch (ResultValueOf(*access.lhs, operand_kind)) {
    case ResultValue::kNumber:
      diag.Error(kLoc,
                 std::format("'{}' is no member or built-in method of the "
                             "integral or real value an operator yields",
                             kName),
                 Subclause("11.8.1"));
      return;
    case ResultValue::kBits:
      diag.Error(kLoc,
                 std::format("'{}' is no member or built-in method of the "
                             "integral value a concatenation yields",
                             kName),
                 Subclause("11.4.12"));
      return;
    case ResultValue::kString:
      if (std::ranges::find(string_methods, kName) != string_methods.end())
        return;
      diag.Error(kLoc,
                 std::format("'{}' is not a built-in method of the string a "
                             "concatenation yields",
                             kName),
                 Subclause("6.16"));
      return;
    default:
      return;
  }
}

}  // namespace delta
