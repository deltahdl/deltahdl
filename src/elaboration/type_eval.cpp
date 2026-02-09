#include "elaboration/type_eval.h"

#include <algorithm>

#include "elaboration/const_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

uint32_t EvalTypeWidth(const DataType& dtype) {
  // If explicit packed dimensions are present, compute from range.
  if (dtype.packed_dim_left && dtype.packed_dim_right) {
    auto left = ConstEvalInt(dtype.packed_dim_left);
    auto right = ConstEvalInt(dtype.packed_dim_right);
    if (left && right) {
      int64_t hi = *left;
      int64_t lo = *right;
      int64_t w = (hi >= lo) ? (hi - lo + 1) : (lo - hi + 1);
      return static_cast<uint32_t>(w);
    }
  }

  // Built-in type widths per IEEE 1800-2023.
  switch (dtype.kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
      return 1;
    case DataTypeKind::kByte:
      return 8;
    case DataTypeKind::kShortint:
      return 16;
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
    case DataTypeKind::kShortreal:
      return 32;
    case DataTypeKind::kLongint:
    case DataTypeKind::kReal:
    case DataTypeKind::kTime:
    case DataTypeKind::kRealtime:
      return 64;
    case DataTypeKind::kEnum:
      return 32;  // default enum base type is int (32-bit)
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kNamed:
    case DataTypeKind::kEvent:
      return 0;
  }
  return 1;
}

bool Is4stateType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kInteger:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

static const DataType* ResolveNamed(const DataType& dtype,
                                    const TypedefMap& typedefs) {
  if (dtype.kind != DataTypeKind::kNamed) return nullptr;
  auto it = typedefs.find(dtype.type_name);
  return (it != typedefs.end()) ? &it->second : nullptr;
}

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs) {
  const auto* resolved = ResolveNamed(dtype, typedefs);
  return resolved ? EvalTypeWidth(*resolved, typedefs) : EvalTypeWidth(dtype);
}

bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs) {
  const auto* resolved = ResolveNamed(dtype, typedefs);
  return resolved ? Is4stateType(*resolved, typedefs)
                  : Is4stateType(dtype.kind);
}

// --- Width inference (IEEE §11.6) ---

static bool IsComparisonOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kLt || op == TokenKind::kGt ||
         op == TokenKind::kLtEq || op == TokenKind::kGtEq ||
         op == TokenKind::kAmpAmp || op == TokenKind::kPipePipe ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static bool IsShiftOp(TokenKind op) {
  return op == TokenKind::kLtLt || op == TokenKind::kGtGt ||
         op == TokenKind::kLtLtLt || op == TokenKind::kGtGtGt;
}

uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return 32;  // Unsized integer defaults to 32 bits.
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return 64;
    case ExprKind::kStringLiteral:
      return 0;
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;
    case ExprKind::kIdentifier:
      return 0;  // Need variable lookup; return 0 for unknown.
    case ExprKind::kSystemCall:
      return 32;
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kBang) return 1;
      return InferExprWidth(expr->lhs, typedefs);
    case ExprKind::kBinary: {
      if (IsComparisonOp(expr->op)) return 1;
      if (IsShiftOp(expr->op)) return InferExprWidth(expr->lhs, typedefs);
      uint32_t lw = InferExprWidth(expr->lhs, typedefs);
      uint32_t rw = InferExprWidth(expr->rhs, typedefs);
      return std::max(lw, rw);
    }
    case ExprKind::kTernary: {
      uint32_t tw = InferExprWidth(expr->true_expr, typedefs);
      uint32_t fw = InferExprWidth(expr->false_expr, typedefs);
      return std::max(tw, fw);
    }
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements) {
        total += InferExprWidth(el, typedefs);
      }
      return total;
    }
    case ExprKind::kReplicate: {
      auto count = ConstEvalInt(expr->repeat_count);
      uint32_t inner = 0;
      for (const auto* el : expr->elements) {
        inner += InferExprWidth(el, typedefs);
      }
      return count ? static_cast<uint32_t>(*count) * inner : inner;
    }
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
    case ExprKind::kCall:
      return 0;
  }
  return 0;
}

uint32_t ContextWidth(const Expr* expr, uint32_t ctx_width,
                      const TypedefMap& typedefs) {
  uint32_t self_width = InferExprWidth(expr, typedefs);
  return std::max(self_width, ctx_width);
}

}  // namespace delta
