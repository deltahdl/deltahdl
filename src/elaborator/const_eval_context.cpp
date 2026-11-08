#include <algorithm>
#include <cstdint>
#include <optional>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

bool OperandsSelfDetermined(TokenKind op) {
  switch (op) {
    case TokenKind::kAmpAmp:
    case TokenKind::kPipePipe:
    case TokenKind::kArrow:
    case TokenKind::kLtDashGt:
      return true;
    default:
      return false;
  }
}

bool OperandsSizedToEachOther(TokenKind op) {
  switch (op) {
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kLtEq:
    case TokenKind::kGtEq:
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
      return true;
    default:
      return false;
  }
}

FoldContext SharedContext(const ConstVal& a, const ConstVal& b) {
  return {std::max(a.width, b.width), !(a.is_signed && b.is_signed)};
}

bool FoldedOutside(const ConstVal& v, FoldContext ctx) {
  return v.width < ctx.width || (v.is_signed && ctx.read_unsigned);
}

std::optional<uint32_t> CastWidth(const Expr* expr, const ScopeMap& scope) {
  if (expr->rhs == nullptr) return CastTargetWidth(expr->text);
  auto size = ConstEvalFull(expr->rhs, scope);
  if (!size || size->value <= 0) return std::nullopt;
  return static_cast<uint32_t>(size->value);
}

}  // namespace

bool AnswersOneBit(TokenKind op) {
  return OperandsSelfDetermined(op) || OperandsSizedToEachOther(op);
}

ConstVal ReadInContext(const ConstVal& v, FoldContext ctx) {
  uint32_t width = std::max(v.width, ctx.width);
  bool is_signed = v.is_signed && !ctx.read_unsigned;
  if (width == v.width && is_signed == v.is_signed) return v;
  return ConstValOfWords(ExtendedWords(v, width, is_signed), width, is_signed);
}

std::optional<BinaryOperands> FoldBinaryOperands(const Expr* expr,
                                                 const ScopeMap& scope,
                                                 FoldContext ctx) {
  const TokenKind kOp = expr->op;
  const bool kLeftOnly = SizedByLeftOperand(kOp);
  const bool kOneBit = AnswersOneBit(kOp);
  const FoldContext kLeftCtx = kOneBit ? FoldContext{} : ctx;
  const FoldContext kRightCtx = kOneBit || kLeftOnly ? FoldContext{} : ctx;
  auto lhs = ConstEvalFull(expr->lhs, scope, kLeftCtx);
  auto rhs = ConstEvalFull(expr->rhs, scope, kRightCtx);
  if (!lhs || !rhs) return std::nullopt;
  if (kLeftOnly || OperandsSelfDetermined(kOp))
    return BinaryOperands{*lhs, *rhs};
  const FoldContext kShared = SharedContext(*lhs, *rhs);
  if (FoldedOutside(*lhs, kShared))
    lhs = ConstEvalFull(expr->lhs, scope, kShared);
  if (FoldedOutside(*rhs, kShared))
    rhs = ConstEvalFull(expr->rhs, scope, kShared);
  if (!lhs || !rhs) return std::nullopt;
  return BinaryOperands{*lhs, *rhs};
}

std::optional<ConstVal> ConstEvalCastFull(const Expr* expr,
                                          const ScopeMap& scope) {
  if (expr->text == "void") return std::nullopt;
  const bool kKeepsWidth = expr->text == "const" || expr->text == "signed" ||
                           expr->text == "unsigned";
  std::optional<uint32_t> width =
      kKeepsWidth ? std::optional<uint32_t>{0} : CastWidth(expr, scope);
  if (!width) return std::nullopt;
  auto operand = ConstEvalFull(expr->lhs, scope, FoldContext{*width});
  if (!operand) return std::nullopt;
  if (expr->text == "signed" || expr->text == "unsigned")
    return CastConstVal(*operand, operand->width, expr->text == "signed");
  if (expr->text == "const" || *width == 0) return operand;
  const bool kSizeCast =
      expr->rhs != nullptr || (expr->text[0] >= '0' && expr->text[0] <= '9');
  return CastConstVal(*operand, *width,
                      kSizeCast ? operand->is_signed
                                : TypeNameToDataType(expr->text).is_signed);
}

std::optional<ConstVal> ConstEvalTernaryFull(const Expr* expr,
                                             const ScopeMap& scope,
                                             FoldContext ctx) {
  auto cond = ConstEvalFull(expr->condition, scope);
  if (!cond) return std::nullopt;
  const bool kTrue = ConstValIsNonZero(*cond);
  const Expr* arm = kTrue ? expr->true_expr : expr->false_expr;
  auto chosen = ConstEvalFull(arm, scope);
  auto other = ConstEvalFull(kTrue ? expr->false_expr : expr->true_expr, scope);
  if (chosen && other) {
    const FoldContext kShared = SharedContext(*chosen, *other);
    ctx = {std::max(ctx.width, kShared.width),
           ctx.read_unsigned || kShared.read_unsigned};
  }
  return ConstEvalFull(arm, scope, ctx);
}

}  // namespace delta
