#include "elaboration/type_eval.h"

#include <algorithm>
#include <cstdlib>

#include "elaboration/const_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

// Compute the bit-width of a single struct/union member.
uint32_t EvalStructMemberWidth(const StructMember& m) {
  // If the member has explicit packed dimensions, use them.
  if (m.packed_dim_left && m.packed_dim_right) {
    auto left = ConstEvalInt(m.packed_dim_left);
    auto right = ConstEvalInt(m.packed_dim_right);
    if (left && right) {
      auto w = std::abs(*left - *right) + 1;
      return static_cast<uint32_t>(w);
    }
  }
  // Default widths for common types.
  switch (m.type_kind) {
    case DataTypeKind::kByte:
      return 8;
    case DataTypeKind::kShortint:
      return 16;
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
      return 32;
    case DataTypeKind::kLongint:
      return 64;
    default:
      return 1;  // bit, logic, reg default to 1.
  }
}

// §7.3.2: Compute ⌈log₂(n)⌉ tag bits for a tagged packed union.
static uint32_t TagBitWidth(uint32_t num_members) {
  uint32_t bits = 0;
  while ((1u << bits) < num_members) ++bits;
  return bits;
}

// §7.2/§7.3: Compute total width of a packed struct or union from members.
static uint32_t EvalStructOrUnionWidth(const DataType& dtype) {
  if (dtype.struct_members.empty()) return 0;
  if (dtype.kind == DataTypeKind::kUnion) {
    uint32_t max_w = 0;
    for (const auto& m : dtype.struct_members) {
      max_w = std::max(max_w, EvalStructMemberWidth(m));
    }
    // §7.3.2: Tagged packed unions include tag bits.
    if (dtype.is_tagged && dtype.is_packed)
      max_w += TagBitWidth(static_cast<uint32_t>(dtype.struct_members.size()));
    return max_w;
  }
  uint32_t total = 0;
  for (const auto& m : dtype.struct_members) {
    total += EvalStructMemberWidth(m);
  }
  return total;
}

// Compute width from explicit [left:right] packed dimension range.
static uint32_t EvalRangeWidth(const Expr* left_expr, const Expr* right_expr) {
  auto left = ConstEvalInt(left_expr);
  auto right = ConstEvalInt(right_expr);
  if (!left || !right) return 0;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

uint32_t EvalTypeWidth(const DataType& dtype) {
  // If explicit packed dimensions are present, compute from range.
  if (dtype.packed_dim_left && dtype.packed_dim_right) {
    uint32_t w = EvalRangeWidth(dtype.packed_dim_left, dtype.packed_dim_right);
    // §7.4.1: Multiply by extra packed dimensions (e.g., [3:0][7:0]).
    for (const auto& [left, right] : dtype.extra_packed_dims) {
      w *= EvalRangeWidth(left, right);
    }
    if (w > 0) return w;
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
      return EvalStructOrUnionWidth(dtype);
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kNamed:
    case DataTypeKind::kEvent:
      return 0;
    case DataTypeKind::kChandle:
      return 64;  // §6.14: Platform-dependent, at least pointer-sized.
    case DataTypeKind::kWire:
    case DataTypeKind::kTri:
    case DataTypeKind::kWand:
    case DataTypeKind::kWor:
    case DataTypeKind::kTriand:
    case DataTypeKind::kTrior:
    case DataTypeKind::kTri0:
    case DataTypeKind::kTri1:
    case DataTypeKind::kTrireg:
    case DataTypeKind::kSupply0:
    case DataTypeKind::kSupply1:
    case DataTypeKind::kUwire:
      return 1;  // Scalar net default width.
    case DataTypeKind::kVirtualInterface:
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

bool IsImplicitlySigned(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kInteger:
    case DataTypeKind::kInt:
    case DataTypeKind::kShortint:
    case DataTypeKind::kLongint:
    case DataTypeKind::kByte:
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

// --- Type compatibility (IEEE §6.22) ---

// §6.11: Return true if the type kind is an integral type.
static bool IsIntegralKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
    case DataTypeKind::kEnum:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

bool TypesMatch(const DataType& a, const DataType& b) {
  if (a.kind != b.kind) return false;
  if (a.is_signed != b.is_signed) return false;
  if (a.kind == DataTypeKind::kNamed) return a.type_name == b.type_name;
  return true;
}

bool TypesEquivalent(const DataType& a, const DataType& b) {
  if (TypesMatch(a, b)) return true;
  // §6.22.2c: Packed/integral types equivalent if same width, signing,
  // and state-ness (both 2-state or both 4-state).
  uint32_t wa = EvalTypeWidth(a);
  uint32_t wb = EvalTypeWidth(b);
  if (wa != wb || wa == 0 || a.is_signed != b.is_signed) return false;
  return Is4stateType(a.kind) == Is4stateType(b.kind);
}

bool IsAssignmentCompatible(const DataType& a, const DataType& b) {
  if (TypesEquivalent(a, b)) return true;
  // §6.22.3: All integral types are assignment compatible with each other.
  if (IsIntegralKind(a.kind) && IsIntegralKind(b.kind)) return true;
  // §6.22.3: enum → integral is assignment compatible.
  if (a.kind == DataTypeKind::kEnum && IsIntegralKind(b.kind)) return true;
  if (b.kind == DataTypeKind::kEnum && IsIntegralKind(a.kind)) return true;
  // Real types are assignment compatible with integral types.
  bool a_real =
      (a.kind == DataTypeKind::kReal || a.kind == DataTypeKind::kShortreal ||
       a.kind == DataTypeKind::kRealtime);
  bool b_real =
      (b.kind == DataTypeKind::kReal || b.kind == DataTypeKind::kShortreal ||
       b.kind == DataTypeKind::kRealtime);
  if ((a_real && IsIntegralKind(b.kind)) ||
      (b_real && IsIntegralKind(a.kind))) {
    return true;
  }
  return a_real && b_real;
}

bool IsCastCompatible(const DataType& a, const DataType& b) {
  if (IsAssignmentCompatible(a, b)) return true;
  // §6.22.4: integral → enum requires explicit cast but is cast compatible.
  if (IsIntegralKind(a.kind) && b.kind == DataTypeKind::kEnum) return true;
  if (IsIntegralKind(b.kind) && a.kind == DataTypeKind::kEnum) return true;
  return false;
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
    case ExprKind::kTypeRef:
      return InferExprWidth(expr->lhs, typedefs);
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
    case ExprKind::kCall:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kCast:
    case ExprKind::kPostfixUnary:
    case ExprKind::kInside:
    case ExprKind::kStreamingConcat:
    case ExprKind::kMinTypMax:
    case ExprKind::kTagged:
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
