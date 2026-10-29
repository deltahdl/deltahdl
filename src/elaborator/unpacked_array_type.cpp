#include "elaborator/unpacked_array_type.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The longest run of typedef names WithTypedefDims reads through, past which
// the names are taken to run in a cycle.
constexpr int kMaxTypedefNames = 16;

DataType NamedType(std::string_view scope, std::string_view name) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.scope_name = scope;
  named.type_name = name;
  return named;
}

// §7.4.2: the left and right bounds of the fixed-size dimension `dim`, a size
// `[n]` being `[0:n-1]`.
std::optional<std::pair<int64_t, int64_t>> FixedBounds(
    const Expr* dim, const ScopeMap& constants) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    std::optional<int64_t> left = ConstEvalInt(dim->lhs, constants);
    std::optional<int64_t> right = ConstEvalInt(dim->rhs, constants);
    if (!left || !right) return std::nullopt;
    return std::pair{*left, *right};
  }
  std::optional<int64_t> size = ConstEvalInt(dim, constants);
  if (!size || *size <= 0) return std::nullopt;
  return std::pair{int64_t{0}, *size - 1};
}

bool IsWildcard(const Expr* dim) {
  return dim->kind == ExprKind::kIdentifier && dim->text == "*";
}

// §6.22.1(f) with §7.8.1: two associative dimensions index alike where both
// are wildcards, or where their index types match, a class matching only
// itself (§6.22.1(d)).
std::optional<bool> SameIndexType(const Expr* a, const Expr* b,
                                  const TypeMatcher& match) {
  if (IsWildcard(a) || IsWildcard(b)) return IsWildcard(a) && IsWildcard(b);
  std::optional<DataType> index_a = IndexDimType(a);
  std::optional<DataType> index_b = IndexDimType(b);
  if (!index_a || !index_b) return std::nullopt;
  return match(*index_a, *index_b);
}

std::optional<bool> SameUnpackedDim(const Expr* a, const Expr* b,
                                    const TypeShapeTables& tables,
                                    const ScopeMap& constants,
                                    const TypeMatcher& match) {
  const UnpackedKind kKind = UnpackedDimKind(a, tables);
  if (kKind != UnpackedDimKind(b, tables)) return false;
  if (kKind == UnpackedKind::kAssociative) return SameIndexType(a, b, match);
  if (kKind != UnpackedKind::kFixed) return true;
  auto bounds_a = FixedBounds(a, constants);
  auto bounds_b = FixedBounds(b, constants);
  if (!bounds_a || !bounds_b) return std::nullopt;
  return *bounds_a == *bounds_b;
}

}  // namespace

UnpackedKind UnpackedDimKind(const Expr* dim, const TypeShapeTables& tables) {
  if (dim == nullptr) return UnpackedKind::kDynamic;
  if (IsQueueDim(dim)) return UnpackedKind::kQueue;
  if (IsFixedSizeUnpackedDim(dim, tables)) return UnpackedKind::kFixed;
  return UnpackedKind::kAssociative;
}

std::optional<DataType> IndexDimType(const Expr* dim) {
  if (dim == nullptr) return std::nullopt;
  if (dim->kind == ExprKind::kTypeRef) {
    if (dim->type_value == nullptr) return std::nullopt;
    return *dim->type_value;
  }
  if (dim->kind == ExprKind::kMemberAccess && dim->is_scope_resolution)
    return NamedType(dim->lhs->text, dim->rhs->text);
  if (dim->kind != ExprKind::kIdentifier || IsWildcard(dim))
    return std::nullopt;
  DataType index = TypeNameToDataType(dim->text);
  if (index.kind == DataTypeKind::kNamed) return index;
  if (dim->op == TokenKind::kKwSigned) index.is_signed = true;
  if (dim->op == TokenKind::kKwUnsigned) index.is_signed = false;
  for (const Expr* packed : dim->elements) {
    if (index.packed_dim_left == nullptr) {
      index.packed_dim_left = packed->lhs;
      index.packed_dim_right = packed->rhs;
    } else {
      index.extra_packed_dims.emplace_back(packed->lhs, packed->rhs);
    }
  }
  return index;
}

UnpackedArrayType WithTypedefDims(const DataType& element,
                                  std::vector<Expr*> dims,
                                  const TypeShapeTables& tables) {
  UnpackedArrayType array{element, dims};
  const DataType* at = &element;
  for (int names = 0; names < kMaxTypedefNames; ++names) {
    if (at->kind != DataTypeKind::kNamed || !at->scope_name.empty()) break;
    auto named = tables.typedefs.find(at->type_name);
    if (named == tables.typedefs.end()) break;
    auto written = tables.typedef_dims.find(at->type_name);
    if (written != tables.typedef_dims.end()) {
      dims.insert(dims.end(), written->second.begin(), written->second.end());
      array = UnpackedArrayType{named->second, dims};
    }
    at = &named->second;
  }
  return array;
}

std::optional<bool> UnpackedArrayTypesMatch(const UnpackedArrayType& a,
                                            const UnpackedArrayType& b,
                                            const TypeShapeTables& tables,
                                            const ScopeMap& constants,
                                            const TypeMatcher& match) {
  if (a.dims.size() != b.dims.size()) return false;
  for (size_t k = 0; k < a.dims.size(); ++k) {
    std::optional<bool> same =
        SameUnpackedDim(a.dims[k], b.dims[k], tables, constants, match);
    if (!same || !*same) return same;
  }
  return match(a.element, b.element);
}

}  // namespace delta
