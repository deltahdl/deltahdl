#include "elaborator/type_eval.h"

#include <algorithm>
#include <cstdlib>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

namespace {
// §7.2.1: the bit width contributed by a member's packed dimensions — the
// leading [l:r] times every trailing dimension. Returns 1 when the member has
// no packed dimension, and 0 when any bound is not a foldable constant.
uint32_t PackedDimProduct(const StructMember& m) {
  if (!m.packed_dim_left || !m.packed_dim_right) return 1;
  auto left = ConstEvalInt(m.packed_dim_left);
  auto right = ConstEvalInt(m.packed_dim_right);
  if (!left || !right) return 0;
  auto w = static_cast<uint32_t>(std::abs(*left - *right) + 1);
  for (const auto& [l, r] : m.extra_packed_dims) {
    auto lv = ConstEvalInt(l);
    auto rv = ConstEvalInt(r);
    if (!lv || !rv) return 0;
    w *= static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  }
  return w;
}
}  // namespace

uint32_t EvalStructMemberWidth(const StructMember& m) {
  // §7.2.1: an inline aggregate (struct/union) or enum member's width comes
  // from its full type, which already folds in its own packed dimensions and
  // (for aggregates) the widths of its nested members.
  if (m.nested_type) return EvalTypeWidth(*m.nested_type);

  if (m.packed_dim_left && m.packed_dim_right) {
    uint32_t w = PackedDimProduct(m);
    if (w > 0) return w;
  }

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
    case DataTypeKind::kVoid:
      return 0;
    default:
      return 1;
  }
}

static uint32_t TagBitWidth(uint32_t num_members) {
  uint32_t bits = 0;
  while ((1u << bits) < num_members) ++bits;
  return bits;
}

uint32_t EvalStructMemberWidth(const StructMember& m,
                               const TypedefMap& typedefs) {
  if (m.nested_type) return EvalTypeWidth(*m.nested_type, typedefs);
  if (m.packed_dim_left && m.packed_dim_right) {
    uint32_t w = PackedDimProduct(m);
    if (w > 0) return w;
  }
  if (m.type_kind == DataTypeKind::kNamed && !m.type_name.empty()) {
    auto it = typedefs.find(m.type_name);
    if (it != typedefs.end()) return EvalTypeWidth(it->second, typedefs);
  }
  return EvalStructMemberWidth(m);
}

static uint32_t EvalStructOrUnionWidth(const DataType& dtype) {
  if (dtype.struct_members.empty()) return 0;
  if (dtype.kind == DataTypeKind::kUnion) {
    uint32_t max_w = 0;
    for (const auto& m : dtype.struct_members) {
      max_w = std::max(max_w, EvalStructMemberWidth(m));
    }

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

static uint32_t EvalStructOrUnionWidth(const DataType& dtype,
                                       const TypedefMap& typedefs) {
  if (dtype.struct_members.empty()) return 0;
  if (dtype.kind == DataTypeKind::kUnion) {
    uint32_t max_w = 0;
    for (const auto& m : dtype.struct_members) {
      max_w = std::max(max_w, EvalStructMemberWidth(m, typedefs));
    }
    if (dtype.is_tagged && dtype.is_packed)
      max_w += TagBitWidth(static_cast<uint32_t>(dtype.struct_members.size()));
    return max_w;
  }
  uint32_t total = 0;
  for (const auto& m : dtype.struct_members) {
    total += EvalStructMemberWidth(m, typedefs);
  }
  return total;
}

uint32_t TaggedUnionTagWidth(const DataType& dtype) {
  if (dtype.kind != DataTypeKind::kUnion) return 0;
  if (!dtype.is_tagged || !dtype.is_packed) return 0;
  if (dtype.struct_members.empty()) return 0;
  return TagBitWidth(static_cast<uint32_t>(dtype.struct_members.size()));
}

uint32_t TaggedUnionTagBitOffset(const DataType& dtype) {
  uint32_t tag_w = TaggedUnionTagWidth(dtype);
  if (tag_w == 0) return 0;
  uint32_t total = EvalTypeWidth(dtype);
  return total - tag_w;
}

static uint32_t EvalRangeWidth(const Expr* left_expr, const Expr* right_expr) {
  auto left = ConstEvalInt(left_expr);
  auto right = ConstEvalInt(right_expr);
  if (!left || !right) return 0;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

static uint32_t EvalRangeWidth(const Expr* left_expr, const Expr* right_expr,
                               const ScopeMap& scope) {
  auto left = ConstEvalInt(left_expr, scope);
  auto right = ConstEvalInt(right_expr, scope);
  if (!left || !right) return 0;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

uint32_t EvalTypeWidth(const DataType& dtype) {
  if (dtype.packed_dim_left && dtype.packed_dim_right) {
    uint32_t w = EvalRangeWidth(dtype.packed_dim_left, dtype.packed_dim_right);

    for (const auto& [left, right] : dtype.extra_packed_dims) {
      w *= EvalRangeWidth(left, right);
    }
    if (w > 0) return w;
  }

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
      return 32;
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      return EvalStructOrUnionWidth(dtype);
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kNamed:
    case DataTypeKind::kEvent:
      return 0;
    case DataTypeKind::kChandle:
      return 64;
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
      return 1;
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
    case DataTypeKind::kTime:
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
  if (resolved) return EvalTypeWidth(*resolved, typedefs);
  if (dtype.kind == DataTypeKind::kStruct ||
      dtype.kind == DataTypeKind::kUnion) {
    if (dtype.packed_dim_left && dtype.packed_dim_right) {
      uint32_t w =
          EvalRangeWidth(dtype.packed_dim_left, dtype.packed_dim_right);
      for (const auto& [left, right] : dtype.extra_packed_dims) {
        w *= EvalRangeWidth(left, right);
      }
      if (w > 0) return w;
    }
    return EvalStructOrUnionWidth(dtype, typedefs);
  }
  return EvalTypeWidth(dtype);
}

uint32_t EvalTypeWidth(const DataType& dtype, const TypedefMap& typedefs,
                       const ScopeMap& scope) {
  const auto* resolved = ResolveNamed(dtype, typedefs);
  if (resolved) return EvalTypeWidth(*resolved, typedefs, scope);
  if (dtype.packed_dim_left && dtype.packed_dim_right) {
    uint32_t w =
        EvalRangeWidth(dtype.packed_dim_left, dtype.packed_dim_right, scope);
    for (const auto& [left, right] : dtype.extra_packed_dims) {
      w *= EvalRangeWidth(left, right, scope);
    }
    if (w > 0) return w;
  }
  return EvalTypeWidth(dtype);
}

static bool Is4stateEnum(const DataType& dtype, const TypedefMap& typedefs) {
  if (!dtype.enum_base_name.empty()) {
    auto it = typedefs.find(dtype.enum_base_name);
    if (it != typedefs.end()) return Is4stateType(it->second, typedefs);
  }
  if (dtype.enum_base_kind != DataTypeKind::kImplicit) {
    return Is4stateType(dtype.enum_base_kind);
  }
  return false;
}

static bool Is4statePackedAggregate(const DataType& dtype) {
  if ((dtype.kind == DataTypeKind::kStruct ||
       dtype.kind == DataTypeKind::kUnion) &&
      (dtype.is_packed || dtype.is_soft)) {
    for (const auto& m : dtype.struct_members) {
      if (Is4stateType(m.type_kind)) return true;
    }
  }
  return false;
}

bool Is4stateType(const DataType& dtype, const TypedefMap& typedefs) {
  const auto* resolved = ResolveNamed(dtype, typedefs);
  if (resolved) return Is4stateType(*resolved, typedefs);

  if (dtype.kind == DataTypeKind::kEnum) return Is4stateEnum(dtype, typedefs);
  if (Is4stateType(dtype.kind)) return true;
  if (Is4statePackedAggregate(dtype)) return true;

  if (dtype.kind == DataTypeKind::kUnion && !dtype.is_packed &&
      !dtype.is_soft && !dtype.struct_members.empty()) {
    return Is4stateType(dtype.struct_members[0].type_kind);
  }
  return false;
}

bool IsSignedType(const DataType& dtype, const TypedefMap& typedefs) {
  const auto* resolved = ResolveNamed(dtype, typedefs);
  return resolved ? IsSignedType(*resolved, typedefs)
                  : (dtype.is_signed || IsImplicitlySigned(dtype.kind));
}

bool IsVector(const DataType& dtype) {
  if (!dtype.packed_dim_left || !dtype.packed_dim_right) return false;
  if (!dtype.extra_packed_dims.empty()) return false;
  switch (dtype.kind) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

bool IsVector(const DataType& dtype, const TypedefMap& typedefs) {
  const auto* resolved = ResolveNamed(dtype, typedefs);
  return resolved ? IsVector(*resolved, typedefs) : IsVector(dtype);
}

bool IsAggregateType(const DataType& dtype) {
  if (dtype.kind == DataTypeKind::kStruct || dtype.kind == DataTypeKind::kUnion)
    return !(dtype.is_packed || dtype.is_soft);
  return false;
}

bool IsSingularType(const DataType& dtype) { return !IsAggregateType(dtype); }

bool IsIntegralType(DataTypeKind kind) {
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

bool IsSimpleBitVectorType(DataTypeKind kind) {
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
      return true;
    default:
      return false;
  }
}

bool IsSimpleBitVectorType(const DataType& dtype) {
  if ((dtype.kind == DataTypeKind::kStruct ||
       dtype.kind == DataTypeKind::kUnion) &&
      (dtype.is_packed || dtype.is_soft))
    return false;

  if (!dtype.extra_packed_dims.empty()) return false;
  return IsSimpleBitVectorType(dtype.kind);
}

static bool HasPredefinedWidth(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

static bool IsSimpleBitVector(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
         kind == DataTypeKind::kReg;
}

static DataTypeKind CanonKind(DataTypeKind k) {
  return k == DataTypeKind::kReg ? DataTypeKind::kLogic : k;
}

static bool VectorMatchesPredef(const DataType& vec, const DataType& predef) {
  if (Is4stateType(vec.kind) != Is4stateType(predef.kind)) return false;
  if (!vec.packed_dim_left || !vec.packed_dim_right) return false;
  if (!vec.extra_packed_dims.empty()) return false;
  auto left = ConstEvalInt(vec.packed_dim_left);
  auto right = ConstEvalInt(vec.packed_dim_right);
  if (!left || !right || *right != 0 || *left < 0) return false;
  auto vec_width = static_cast<uint32_t>(*left + 1);
  return vec_width == EvalTypeWidth(predef);
}

bool TypesMatch(const DataType& a, const DataType& b) {
  if (a.is_signed != b.is_signed) return false;

  if (CanonKind(a.kind) == CanonKind(b.kind)) {
    if (a.kind == DataTypeKind::kNamed) return a.type_name == b.type_name;
    return true;
  }

  if (IsSimpleBitVector(a.kind) && HasPredefinedWidth(b.kind)) {
    return VectorMatchesPredef(a, b);
  }
  if (HasPredefinedWidth(a.kind) && IsSimpleBitVector(b.kind)) {
    return VectorMatchesPredef(b, a);
  }
  return false;
}

static bool IsPackedOrIntegral(const DataType& dtype) {
  if (IsIntegralType(dtype.kind)) return true;
  if ((dtype.kind == DataTypeKind::kStruct ||
       dtype.kind == DataTypeKind::kUnion) &&
      (dtype.is_packed || dtype.is_soft))
    return true;
  return false;
}

static bool Is4stateForEquivalence(const DataType& dtype) {
  if (Is4stateType(dtype.kind)) return true;
  if ((dtype.kind == DataTypeKind::kStruct ||
       dtype.kind == DataTypeKind::kUnion) &&
      (dtype.is_packed || dtype.is_soft)) {
    for (const auto& m : dtype.struct_members) {
      if (Is4stateType(m.type_kind)) return true;
    }
  }
  return false;
}

bool TypesEquivalent(const DataType& a, const DataType& b) {
  if (TypesMatch(a, b)) return true;

  if (!IsPackedOrIntegral(a) || !IsPackedOrIntegral(b)) return false;
  uint32_t wa = EvalTypeWidth(a);
  uint32_t wb = EvalTypeWidth(b);
  if (wa != wb || wa == 0 || a.is_signed != b.is_signed) return false;
  return Is4stateForEquivalence(a) == Is4stateForEquivalence(b);
}

bool ElementTypesEquivalent(const ElementTypeInfo& a,
                            const ElementTypeInfo& b) {
  if (CanonKind(a.kind) == CanonKind(b.kind) && a.is_signed == b.is_signed &&
      a.width == b.width && a.is_4state == b.is_4state) {
    return true;
  }

  if (IsIntegralType(a.kind) && IsIntegralType(b.kind)) {
    return a.width == b.width && a.width > 0 && a.is_signed == b.is_signed &&
           a.is_4state == b.is_4state;
  }
  return false;
}

bool IsAssignmentCompatible(const DataType& a, const DataType& b) {
  if (TypesEquivalent(a, b)) return true;

  if (IsIntegralType(a.kind) && IsIntegralType(b.kind)) return true;

  if (a.kind == DataTypeKind::kEnum && IsIntegralType(b.kind)) return true;

  bool a_real =
      (a.kind == DataTypeKind::kReal || a.kind == DataTypeKind::kShortreal ||
       a.kind == DataTypeKind::kRealtime);
  bool b_real =
      (b.kind == DataTypeKind::kReal || b.kind == DataTypeKind::kShortreal ||
       b.kind == DataTypeKind::kRealtime);
  if ((a_real && IsIntegralType(b.kind)) ||
      (b_real && IsIntegralType(a.kind))) {
    return true;
  }
  return a_real && b_real;
}

bool IsCastCompatible(const DataType& a, const DataType& b) {
  if (IsAssignmentCompatible(a, b)) return true;

  if (IsIntegralType(a.kind) && b.kind == DataTypeKind::kEnum) return true;
  if (IsIntegralType(b.kind) && a.kind == DataTypeKind::kEnum) return true;
  return false;
}

// §6.22.5: a chandle is one of the handle types the clause singles out as
// type-incompatible with every type other than itself. (Class handles and
// interface class handles are spelled with named types and are covered by the
// residual rule below: a named type is never integral, real, or an enum, so it
// is cast-compatible only with the same named type and incompatible with all
// others.)
static bool IsHandleType(const DataType& dtype) {
  return dtype.kind == DataTypeKind::kChandle;
}

bool IsTypeIncompatible(const DataType& a, const DataType& b) {
  // The handle types named by §6.22.5 are incompatible with every type that is
  // not the same handle type; no implicit or explicit cast can bridge them.
  if (IsHandleType(a) || IsHandleType(b)) return !TypesMatch(a, b);

  // Otherwise type-incompatible is the residual: the nonequivalent types with
  // no implicit or explicit casting rule, i.e. anything not cast-compatible.
  return !IsCastCompatible(a, b);
}

static bool IsOneBitResultOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kLt || op == TokenKind::kGt ||
         op == TokenKind::kLtEq || op == TokenKind::kGtEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion ||
         op == TokenKind::kAmpAmp || op == TokenKind::kPipePipe ||
         op == TokenKind::kArrow || op == TokenKind::kLtDashGt;
}

static bool IsReductionOp(TokenKind op) {
  return op == TokenKind::kAmp || op == TokenKind::kTildeAmp ||
         op == TokenKind::kPipe || op == TokenKind::kTildePipe ||
         op == TokenKind::kCaret || op == TokenKind::kTildeCaret ||
         op == TokenKind::kCaretTilde;
}

static uint32_t KeywordCastWidth(std::string_view type_name, bool* matched) {
  *matched = true;
  if (type_name == "byte") return 8;
  if (type_name == "shortint") return 16;
  if (type_name == "int") return 32;
  if (type_name == "longint") return 64;
  if (type_name == "integer") return 32;
  if (type_name == "real" || type_name == "realtime") return 64;
  if (type_name == "shortreal") return 32;
  if (type_name == "bit") return 1;
  if (type_name == "logic") return 1;
  if (type_name == "reg") return 1;
  if (type_name == "string") return 0;
  *matched = false;
  return 0;
}

static uint32_t LeadingDecimalWidth(std::string_view type_name) {
  if (type_name.empty() || type_name[0] < '0' || type_name[0] > '9') return 0;
  uint32_t w = 0;
  for (char c : type_name) {
    if (c >= '0' && c <= '9')
      w = w * 10 + (c - '0');
    else
      break;
  }
  return w;
}

uint32_t CastTargetWidth(std::string_view type_name) {
  bool matched = false;
  uint32_t kw = KeywordCastWidth(type_name, &matched);
  if (matched) return kw;
  return LeadingDecimalWidth(type_name);
}

static bool IsShiftOp(TokenKind op) {
  return op == TokenKind::kLtLt || op == TokenKind::kGtGt ||
         op == TokenKind::kLtLtLt || op == TokenKind::kGtGtGt;
}

static uint32_t InferBinaryWidth(const Expr* expr, const TypedefMap& typedefs) {
  if (IsOneBitResultOp(expr->op)) return 1;
  if (IsShiftOp(expr->op)) return InferExprWidth(expr->lhs, typedefs);
  if (expr->op == TokenKind::kPower) return InferExprWidth(expr->lhs, typedefs);
  uint32_t lw = InferExprWidth(expr->lhs, typedefs);
  uint32_t rw = InferExprWidth(expr->rhs, typedefs);
  return std::max(lw, rw);
}

static uint32_t InferElementsTotalWidth(const Expr* expr,
                                        const TypedefMap& typedefs) {
  uint32_t total = 0;
  for (const auto* el : expr->elements) {
    total += InferExprWidth(el, typedefs);
  }
  return total;
}

static uint32_t InferReplicateWidth(const Expr* expr,
                                    const TypedefMap& typedefs) {
  auto count = ConstEvalInt(expr->repeat_count);
  uint32_t inner = InferElementsTotalWidth(expr, typedefs);
  return count ? static_cast<uint32_t>(*count) * inner : inner;
}

static uint32_t InferCastWidth(const Expr* expr, const TypedefMap& typedefs) {
  if (expr->text == "signed" || expr->text == "unsigned" ||
      expr->text == "const")
    return InferExprWidth(expr->lhs, typedefs);
  if (expr->text == "void") return 0;
  uint32_t w = CastTargetWidth(expr->text);
  if (w > 0) return w;
  auto it = typedefs.find(expr->text);
  if (it != typedefs.end()) return EvalTypeWidth(it->second);
  return InferExprWidth(expr->lhs, typedefs);
}

uint32_t InferExprWidth(const Expr* expr, const TypedefMap& typedefs) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return ExtractLiteralWidth(expr->text);
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return 64;
    case ExprKind::kStringLiteral:
      return 0;
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;
    case ExprKind::kIdentifier:
      return 0;
    case ExprKind::kSystemCall:
      return 32;
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kBang || IsReductionOp(expr->op)) return 1;
      return InferExprWidth(expr->lhs, typedefs);
    case ExprKind::kBinary:
      return InferBinaryWidth(expr, typedefs);
    case ExprKind::kTernary: {
      uint32_t tw = InferExprWidth(expr->true_expr, typedefs);
      uint32_t fw = InferExprWidth(expr->false_expr, typedefs);
      return std::max(tw, fw);
    }
    case ExprKind::kConcatenation:
      return InferElementsTotalWidth(expr, typedefs);
    case ExprKind::kReplicate:
      return InferReplicateWidth(expr, typedefs);
    case ExprKind::kTypeRef:
      return InferExprWidth(expr->lhs, typedefs);
    case ExprKind::kCast:
      return InferCastWidth(expr, typedefs);
    case ExprKind::kSelect:
    case ExprKind::kMemberAccess:
    case ExprKind::kCall:
    case ExprKind::kAssignmentPattern:
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
