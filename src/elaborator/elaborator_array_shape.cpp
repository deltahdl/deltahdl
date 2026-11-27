#include "elaborator/elaborator_array_shape.h"

#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

DataTypeKind ElementKindThroughTypedefs(const DataType& dtype,
                                        const TypedefMap& typedefs) {
  const DataType* type = &dtype;
  for (int hops = 0; hops < 8 && type->kind == DataTypeKind::kNamed; ++hops) {
    auto td = typedefs.find(type->type_name);
    if (td == typedefs.end()) break;
    type = &td->second;
  }
  return type->kind == DataTypeKind::kEnum ? dtype.kind : type->kind;
}

std::string_view ElementTypeIdentity(const DataType& dtype,
                                     const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  FollowTypedefs(dtype, typedefs, names);
  return names.empty() ? std::string_view{} : names.back();
}

namespace {

std::optional<uint32_t> DimSize(const Expr* dim, const ScopeMap& scope) {
  if (!dim) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto lv = ConstEvalInt(dim->lhs, scope);
    auto rv = ConstEvalInt(dim->rhs, scope);
    if (!lv || !rv) return std::nullopt;
    return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  }
  auto sv = ConstEvalInt(dim, scope);
  if (!sv || *sv <= 0) return std::nullopt;
  return static_cast<uint32_t>(*sv);
}

}  // namespace

const DataType* ElementAggregate(const DataType& dtype,
                                 const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* resolved = FollowTypedefs(dtype, typedefs, names);
  const bool kAggregate =
      resolved != nullptr && (resolved->kind == DataTypeKind::kStruct ||
                              resolved->kind == DataTypeKind::kUnion);
  return kAggregate ? resolved : nullptr;
}

std::vector<std::optional<uint32_t>> ElementUnpackedShape(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        typedef_dims,
    const ScopeMap& scope) {
  std::vector<std::optional<uint32_t>> shape;
  const DataType* type = &dtype;
  for (int hops = 0; hops < 16 && type->kind == DataTypeKind::kNamed; ++hops) {
    auto dims = typedef_dims.find(type->type_name);
    if (dims != typedef_dims.end()) {
      for (const Expr* dim : dims->second) shape.push_back(DimSize(dim, scope));
    }
    auto td = typedefs.find(type->type_name);
    if (td == typedefs.end()) break;
    type = &td->second;
  }
  return shape;
}

std::vector<std::optional<uint32_t>> UnpackedShapeOf(
    const DataType& elem, const std::vector<Expr*>& dims,
    const std::unordered_set<std::string_view>& aggregate_typedefs,
    const ScopeMap& scope) {
  std::vector<std::optional<uint32_t>> shape;
  if (elem.kind == DataTypeKind::kNamed &&
      aggregate_typedefs.count(elem.type_name) > 0) {
    return shape;
  }
  shape.reserve(dims.size());
  for (const auto* dim : dims) shape.push_back(DimSize(dim, scope));
  return shape;
}

}  // namespace delta
