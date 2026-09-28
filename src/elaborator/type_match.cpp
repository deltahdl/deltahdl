#include <algorithm>
#include <cstddef>
#include <cstdint>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

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

// Whether two bounds of a packed dimension are the same: both absent, or both
// present with equal values. A bound that does not fold without a scope, such
// as `W-1`, is not told apart from the other.
static bool SameBound(const Expr* a, const Expr* b) {
  if ((a == nullptr) != (b == nullptr)) return false;
  if (a == nullptr) return true;
  auto va = ConstEvalInt(a);
  auto vb = ConstEvalInt(b);
  return !va || !vb || *va == *vb;
}

// §6.22.1(f): two fixed-size array types match only where they have the same
// left and right bounds, dimension by dimension, so `bit [11:0]` does not
// match `bit [12:0]`, nor `bit [7:0]` match `bit [0:7]`.
static bool SamePackedBounds(const DataType& a, const DataType& b) {
  if (!SameBound(a.packed_dim_left, b.packed_dim_left) ||
      !SameBound(a.packed_dim_right, b.packed_dim_right))
    return false;
  if (a.extra_packed_dims.size() != b.extra_packed_dims.size()) return false;
  for (size_t i = 0; i < a.extra_packed_dims.size(); ++i) {
    if (!SameBound(a.extra_packed_dims[i].first,
                   b.extra_packed_dims[i].first) ||
        !SameBound(a.extra_packed_dims[i].second,
                   b.extra_packed_dims[i].second))
      return false;
  }
  return true;
}

// Whether two unpacked dimensions are the same: a range `[l:r]` bound by bound,
// and a size `[n]` by its value.
static bool SameUnpackedDim(const Expr* a, const Expr* b) {
  bool a_range = a != nullptr && a->kind == ExprKind::kBinary &&
                 a->op == TokenKind::kColon;
  bool b_range = b != nullptr && b->kind == ExprKind::kBinary &&
                 b->op == TokenKind::kColon;
  if (a_range != b_range) return false;
  if (!a_range) return SameBound(a, b);
  return SameBound(a->lhs, b->lhs) && SameBound(a->rhs, b->rhs);
}

// Whether two members of one declaration have the same type: the kind,
// signing, name and dimensions, and a nested aggregate's own members.
static bool SameMember(const StructMember& a, const StructMember& b) {
  if (CanonKind(a.type_kind) != CanonKind(b.type_kind) ||
      a.is_signed != b.is_signed || a.type_name != b.type_name ||
      a.scope_name != b.scope_name)
    return false;
  DataType pa;
  pa.packed_dim_left = a.packed_dim_left;
  pa.packed_dim_right = a.packed_dim_right;
  pa.extra_packed_dims = a.extra_packed_dims;
  DataType pb;
  pb.packed_dim_left = b.packed_dim_left;
  pb.packed_dim_right = b.packed_dim_right;
  pb.extra_packed_dims = b.extra_packed_dims;
  if (!SamePackedBounds(pa, pb)) return false;
  if ((a.nested_type == nullptr) != (b.nested_type == nullptr)) return false;
  if (a.nested_type != nullptr && !TypesMatch(*a.nested_type, *b.nested_type))
    return false;
  return std::equal(a.unpacked_dims.begin(), a.unpacked_dims.end(),
                    b.unpacked_dims.begin(), b.unpacked_dims.end(),
                    SameUnpackedDim);
}

// §6.22.1(c) and (d): an enum, struct or union type matches only a type of
// its own declaration. Two specializations of one class's struct typedef
// (§6.25) share the declaration and are still different types, which the
// members they were specialized to tell apart.
static bool SameDeclaration(const DataType& a, const DataType& b) {
  bool declared = a.kind == DataTypeKind::kEnum ||
                  a.kind == DataTypeKind::kStruct ||
                  a.kind == DataTypeKind::kUnion;
  if (!declared) return true;
  if (a.decl_loc.file_id != b.decl_loc.file_id ||
      a.decl_loc.line != b.decl_loc.line ||
      a.decl_loc.column != b.decl_loc.column)
    return false;
  return std::equal(a.struct_members.begin(), a.struct_members.end(),
                    b.struct_members.begin(), b.struct_members.end(),
                    SameMember);
}

bool TypesMatch(const DataType& a, const DataType& b) {
  if (a.is_signed != b.is_signed) return false;

  if (CanonKind(a.kind) == CanonKind(b.kind)) {
    if (a.kind == DataTypeKind::kNamed) return a.type_name == b.type_name;
    return SameDeclaration(a, b) && SamePackedBounds(a, b);
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

}  // namespace delta
