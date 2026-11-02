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

static bool VectorMatchesPredef(const DataType& vec, const DataType& predef,
                                const ScopeMap& scope) {
  if (Is4stateType(vec.kind) != Is4stateType(predef.kind)) return false;
  if (!vec.packed_dim_left || !vec.packed_dim_right) return false;
  if (!vec.extra_packed_dims.empty()) return false;
  auto left = ConstEvalInt(vec.packed_dim_left, scope);
  auto right = ConstEvalInt(vec.packed_dim_right, scope);
  if (!left || !right || *right != 0 || *left < 0) return false;
  auto vec_width = static_cast<uint32_t>(*left + 1);
  return vec_width == EvalTypeWidth(predef);
}

// Whether two bounds of a packed dimension are the same: both absent, or both
// present with equal values, folded against `scope`, the parameters and genvar
// values in force where the types are written. A bound that does not fold
// there is not told apart from the other.
static bool SameBound(const Expr* a, const Expr* b, const ScopeMap& scope) {
  if ((a == nullptr) != (b == nullptr)) return false;
  if (a == nullptr) return true;
  auto va = ConstEvalInt(a, scope);
  auto vb = ConstEvalInt(b, scope);
  return !va || !vb || *va == *vb;
}

// §6.22.1(f): two fixed-size array types match only where they have the same
// left and right bounds, dimension by dimension, so `bit [11:0]` does not
// match `bit [12:0]`, nor `bit [7:0]` match `bit [0:7]`.
static bool SamePackedBounds(const DataType& a, const DataType& b,
                             const ScopeMap& scope) {
  if (!SameBound(a.packed_dim_left, b.packed_dim_left, scope) ||
      !SameBound(a.packed_dim_right, b.packed_dim_right, scope))
    return false;
  if (a.extra_packed_dims.size() != b.extra_packed_dims.size()) return false;
  for (size_t i = 0; i < a.extra_packed_dims.size(); ++i) {
    if (!SameBound(a.extra_packed_dims[i].first, b.extra_packed_dims[i].first,
                   scope) ||
        !SameBound(a.extra_packed_dims[i].second, b.extra_packed_dims[i].second,
                   scope))
      return false;
  }
  return true;
}

// Whether two unpacked dimensions are the same: a range `[l:r]` bound by bound,
// and a size `[n]` by its value.
static bool SameUnpackedDim(const Expr* a, const Expr* b,
                            const ScopeMap& scope) {
  bool a_range = a != nullptr && a->kind == ExprKind::kBinary &&
                 a->op == TokenKind::kColon;
  bool b_range = b != nullptr && b->kind == ExprKind::kBinary &&
                 b->op == TokenKind::kColon;
  if (a_range != b_range) return false;
  if (!a_range) return SameBound(a, b, scope);
  return SameBound(a->lhs, b->lhs, scope) && SameBound(a->rhs, b->rhs, scope);
}

// Whether two members of one declaration have the same type: the kind,
// signing, name and dimensions, and a nested aggregate's own members.
static bool SameMember(const StructMember& a, const StructMember& b,
                       const ScopeMap& scope) {
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
  if (!SamePackedBounds(pa, pb, scope)) return false;
  if ((a.nested_type == nullptr) != (b.nested_type == nullptr)) return false;
  if (a.nested_type != nullptr &&
      !TypesMatch(*a.nested_type, *b.nested_type, scope))
    return false;
  return std::equal(a.unpacked_dims.begin(), a.unpacked_dims.end(),
                    b.unpacked_dims.begin(), b.unpacked_dims.end(),
                    [&](const Expr* x, const Expr* y) {
                      return SameUnpackedDim(x, y, scope);
                    });
}

// §6.22.1(c) and (d): an enum, struct or union type matches only a type of
// its own declaration. Two specializations of one class's struct typedef
// (§6.25) share the declaration and are still different types, which the
// members they were specialized to tell apart.
static bool SameDeclaration(const DataType& a, const DataType& b,
                            const ScopeMap& scope) {
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
                    [&](const StructMember& x, const StructMember& y) {
                      return SameMember(x, y, scope);
                    });
}

bool TypesMatch(const DataType& a, const DataType& b) {
  return TypesMatch(a, b, ScopeMap{});
}

bool TypesMatch(const DataType& a, const DataType& b, const ScopeMap& scope) {
  if (a.is_signed != b.is_signed) return false;

  if (CanonKind(a.kind) == CanonKind(b.kind)) {
    if (a.kind == DataTypeKind::kNamed) return a.type_name == b.type_name;
    return SameDeclaration(a, b, scope) && SamePackedBounds(a, b, scope);
  }

  if (IsSimpleBitVector(a.kind) && HasPredefinedWidth(b.kind)) {
    return VectorMatchesPredef(a, b, scope);
  }
  if (HasPredefinedWidth(a.kind) && IsSimpleBitVector(b.kind)) {
    return VectorMatchesPredef(b, a, scope);
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
  // §6.22.2: an enumeration or a class is equivalent only to a type matching
  // it, never to another of the same width, so an element type left as a name
  // is judged by the name that identifies it.
  if (a.kind == DataTypeKind::kNamed || b.kind == DataTypeKind::kNamed) {
    return a.kind == b.kind && a.type_name == b.type_name;
  }
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

  // §6.22.3/§6.22.4: assignment compatibility for integral types is symmetric
  // EXCEPT when the target (b) is an enum -- an integral value requires an
  // explicit cast to be assigned to an enum, so an enum target is excluded here
  // and only the legal enum-source direction is accepted by the rule below.
  if (IsIntegralType(a.kind) && IsIntegralType(b.kind) &&
      b.kind != DataTypeKind::kEnum)
    return true;

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

}  // namespace delta
