#include "elaborator/param_value_shape.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/aggregate_shape.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using Kind = ParamValueKind;

constexpr std::array<std::string_view, 14> kNumericCastTypes = {
    "bit",     "logic", "reg",  "byte",      "shortint", "int",    "longint",
    "integer", "time",  "real", "shortreal", "realtime", "signed", "unsigned"};

ParamValueShape OfKind(Kind kind) {
  ParamValueShape shape;
  shape.kind = kind;
  return shape;
}

uint64_t TypeIdentity(const DataType& type) {
  return (uint64_t{type.decl_loc.file_id} << 48) |
         (uint64_t{type.decl_loc.line} << 20) | type.decl_loc.column;
}

bool IsNumeric(Kind kind) {
  return kind == Kind::kNumber || kind == Kind::kEnum ||
         kind == Kind::kStringLiteral;
}

std::vector<uint64_t> DimSizes(const std::vector<Expr*>& dims,
                               const ScopeMap& constants) {
  std::vector<uint64_t> sizes;
  sizes.reserve(dims.size());
  for (const Expr* dim : dims) {
    auto folded = FoldUnpackedDimBounds(dim, constants);
    sizes.push_back(folded ? folded->Size() : 0);
  }
  return sizes;
}

ParamValueShape ArrayShape(std::vector<uint64_t> dims,
                           const DataType& element) {
  ParamValueShape shape = OfKind(Kind::kArray);
  shape.dims = std::move(dims);
  shape.element = element;
  return shape;
}

ParamValueShape StructureShape(const DataType& resolved) {
  ParamValueShape shape = ShapeOfIdentity(Kind::kStructure, resolved);
  shape.structure = resolved;
  return shape;
}

std::size_t WrittenPackedDims(const DataType& type) {
  if (type.kind != DataTypeKind::kNamed) return 0;
  return (type.packed_dim_left != nullptr ? 1 : 0) +
         type.extra_packed_dims.size();
}

std::size_t PackedDimsOver(const DataType& type,
                           const std::vector<std::string_view>& names,
                           const TypedefMap& typedefs) {
  std::size_t dims = WrittenPackedDims(type);
  for (std::string_view name : names)
    dims += WrittenPackedDims(typedefs.at(name));
  return dims;
}

ParamValueShape EnumShape(const DataType& resolved, std::size_t packed_dims) {
  const std::size_t kDims = packed_dims + resolved.enum_array_dims.size();
  ParamValueShape shape =
      ShapeOfIdentity(kDims == 0 ? Kind::kEnum : Kind::kNumber, resolved);
  shape.enum_array_dims = kDims;
  return shape;
}

ParamValueShape ResolvedShape(const DataType& resolved,
                              std::size_t packed_dims) {
  switch (resolved.kind) {
    case DataTypeKind::kEnum:
      return EnumShape(resolved, packed_dims);
    case DataTypeKind::kString:
      return OfKind(Kind::kString);
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      return IsUnpackedAggregateType(resolved) ? StructureShape(resolved)
                                               : OfKind(Kind::kNumber);
    default:
      return OfKind(Kind::kNumber);
  }
}

std::optional<ParamValueShape> TypedefArrayShape(
    const std::vector<std::string_view>& names, const ParamValueScope& scope) {
  for (std::string_view name : names) {
    auto dims = scope.tables.typedef_dims.find(name);
    if (dims == scope.tables.typedef_dims.end()) continue;
    return ArrayShape(DimSizes(dims->second, scope.constants),
                      scope.tables.typedefs.at(name));
  }
  return std::nullopt;
}

ParamValueShape DeclaredShape(const DataType& type, std::vector<uint64_t> dims,
                              const ParamValueScope& scope) {
  if (!dims.empty()) return ArrayShape(std::move(dims), type);
  const std::string kKey = NamedTypeKey(type);
  DataType keyed = type;
  keyed.type_name = kKey;
  std::vector<std::string_view> names;
  const DataType* resolved =
      FollowTypedefs(keyed, scope.tables.typedefs, names);
  if (auto array = TypedefArrayShape(names, scope)) return *std::move(array);
  if (resolved != nullptr)
    return ResolvedShape(*resolved,
                         PackedDimsOver(type, names, scope.tables.typedefs));
  if (scope.tables.class_names.count(names.back()) == 0) return {};
  ParamValueShape shape = OfKind(Kind::kClass);
  shape.class_name = names.back();
  return shape;
}

ParamValueShape NamedShape(const Expr* value, const ParamValueScope& scope) {
  if (value->text == "null") return OfKind(Kind::kNull);
  return (value->scope_prefix.empty()
              ? scope.named(value->text)
              : ScopedParamShape(value->scope_prefix, value->text, scope))
      .value_or(ParamValueShape{});
}

ParamValueShape QualifiedShape(const Expr* value,
                               const ParamValueScope& scope) {
  return ScopedParamShape(value->lhs->text, value->rhs->text, scope)
      .value_or(ParamValueShape{});
}

DataType NamedType(std::string_view scope_name, std::string_view type_name) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.scope_name = scope_name;
  named.type_name = type_name;
  return named;
}

ParamValueShape CastTypeShape(const Expr* type_node,
                              const ParamValueScope& scope) {
  if (type_node->kind != ExprKind::kMemberAccess) return OfKind(Kind::kNumber);
  return DeclaredShape(NamedType(type_node->lhs->text, type_node->rhs->text),
                       {}, scope);
}

ParamValueShape CastShape(const Expr* cast, const ParamValueScope& scope) {
  const std::string_view kType = cast->text;
  if (kType.empty()) return CastTypeShape(cast->rhs, scope);
  if (kType == "const") return ParamValueShapeOf(cast->lhs, scope);
  if (kType == "string") return OfKind(Kind::kString);
  if (std::ranges::find(kNumericCastTypes, kType) != kNumericCastTypes.end())
    return OfKind(Kind::kNumber);
  return DeclaredShape(NamedType({}, kType), {}, scope);
}

ParamValueShape TernaryShape(const Expr* ternary,
                             const ParamValueScope& scope) {
  ParamValueShape when_true = ParamValueShapeOf(ternary->true_expr, scope);
  const ParamValueShape kWhenFalse =
      ParamValueShapeOf(ternary->false_expr, scope);
  if (when_true.kind == kWhenFalse.kind &&
      when_true.identity == kWhenFalse.identity)
    return when_true;
  return OfKind(IsNumeric(when_true.kind) && IsNumeric(kWhenFalse.kind)
                    ? Kind::kNumber
                    : Kind::kUnknown);
}

ParamValueShape ConcatShape(const Expr* concat, const ParamValueScope& scope) {
  bool text = true;
  bool any_string = false;
  for (const Expr* item : concat->elements) {
    const Kind kKind = ParamValueShapeOf(item, scope).kind;
    text = text && (kKind == Kind::kString || kKind == Kind::kStringLiteral);
    any_string = any_string || kKind == Kind::kString;
  }
  if (!text) return OfKind(Kind::kNumber);
  return OfKind(any_string ? Kind::kString : Kind::kStringLiteral);
}

int64_t SliceSize(const Expr& select, const ScopeMap& constants) {
  const std::optional<int64_t> kEnd = ConstEvalInt(select.index_end, constants);
  if (select.is_part_select_plus || select.is_part_select_minus)
    return kEnd.value_or(0);
  return ConstEvalInt(select.index, constants)
      .and_then([&kEnd](int64_t start) {
        return kEnd.transform(
            [start](int64_t end) { return std::abs(start - end) + 1; });
      })
      .value_or(0);
}

ParamValueShape ArrayPartShape(ParamValueShape array, const Expr& select,
                               const ParamValueScope& scope) {
  if (select.index_end != nullptr) {
    array.dims.front() =
        static_cast<uint64_t>(SliceSize(select, scope.constants));
    return array;
  }
  array.dims.erase(array.dims.begin());
  if (!array.dims.empty()) return array;
  return DeclaredShape(array.element, {}, scope);
}

ParamValueShape IntegralSelectShape(ParamValueShape base, const Expr& select) {
  if (base.enum_array_dims == 0) return OfKind(Kind::kNumber);
  if (select.index_end != nullptr) return base;
  --base.enum_array_dims;
  if (base.enum_array_dims == 0) base.kind = Kind::kEnum;
  return base;
}

ParamValueShape SelectShape(const Expr* select, const ParamValueScope& scope) {
  ParamValueShape base = ParamValueShapeOf(select->base, scope);
  switch (base.kind) {
    case Kind::kArray:
      return ArrayPartShape(std::move(base), *select, scope);
    case Kind::kNumber:
    case Kind::kEnum:
    case Kind::kStringLiteral:
    case Kind::kString:
      return IntegralSelectShape(std::move(base), *select);
    default:
      return {};
  }
}

ParamValueShape MemberShape(const Expr* access, const ParamValueScope& scope) {
  const ParamValueShape kBase = ParamValueShapeOf(access->lhs, scope);
  ParamValueShape shape;
  if (kBase.kind != Kind::kStructure) return shape;
  for (const StructMember& member : kBase.structure.struct_members) {
    if (member.name == access->rhs->text)
      shape = ParamTargetShape(MemberWrittenType(member), member.unpacked_dims,
                               scope);
  }
  return shape;
}

bool SameIdentity(const ParamValueShape& target, const ParamValueShape& value) {
  return value.identity == 0 || value.identity == target.identity;
}

const DataType* Resolved(const DataType* type, const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* resolved = FollowTypedefs(*type, typedefs, names);
  return resolved != nullptr ? resolved : type;
}

bool DimsMatch(uint64_t target, uint64_t value) {
  return target == 0 || value == 0 || target == value;
}

bool ArraysAssignable(const ParamValueShape& target,
                      const ParamValueShape& value,
                      const TypedefMap& typedefs) {
  return std::ranges::equal(target.dims, value.dims, DimsMatch) &&
         TypesEquivalent(*Resolved(&target.element, typedefs),
                         *Resolved(&value.element, typedefs));
}

}  // namespace

ParamValueShape ShapeOfIdentity(Kind kind, const DataType& type) {
  ParamValueShape shape = OfKind(kind);
  shape.identity = TypeIdentity(type);
  return shape;
}

ParamValueShape ParamTargetShape(const DataType& type,
                                 const std::vector<Expr*>& dims,
                                 const ParamValueScope& scope) {
  if (type.kind == DataTypeKind::kImplicit) return {};
  return DeclaredShape(type, DimSizes(dims, scope.constants), scope);
}

ParamValueShape ParamDeclTargetShape(const RtlirParamDecl& pd,
                                     const ParamValueScope& scope) {
  static const std::vector<Expr*> kNoDims;
  const DataType* type =
      pd.type_param_actual != nullptr ? pd.type_param_actual : pd.decl_type;
  if (type == nullptr) return {};
  return ParamTargetShape(
      *type, pd.unpacked_dims != nullptr ? *pd.unpacked_dims : kNoDims, scope);
}

ParamValueShape ValueOrTargetShape(const ParamValueShape& target,
                                   const Expr* value,
                                   const ParamValueScope& scope) {
  if (target.kind != ParamValueKind::kUnknown || value == nullptr)
    return target;
  return ParamValueShapeOf(value, scope);
}

std::optional<ParamValueShape> DeclaringEnumShape(const DataType* enumeration) {
  if (enumeration == nullptr) return std::nullopt;
  return ShapeOfIdentity(Kind::kEnum, *enumeration);
}

ParamValueShape ParamValueShapeOf(const Expr* value,
                                  const ParamValueScope& scope) {
  switch (value->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kUnary:
    case ExprKind::kBinary:
      return OfKind(Kind::kNumber);
    case ExprKind::kStringLiteral:
      return OfKind(Kind::kStringLiteral);
    case ExprKind::kIdentifier:
      return NamedShape(value, scope);
    case ExprKind::kSelect:
      return SelectShape(value, scope);
    case ExprKind::kMemberAccess:
      return value->is_scope_resolution ? QualifiedShape(value, scope)
                                        : MemberShape(value, scope);
    case ExprKind::kAssignmentPattern:
      return OfKind(Kind::kPattern);
    case ExprKind::kCast:
      return CastShape(value, scope);
    case ExprKind::kTernary:
      return TernaryShape(value, scope);
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return ConcatShape(value, scope);
    default:
      return {};
  }
}

bool ParamShapeAssignable(const ParamValueShape& target,
                          const ParamValueShape& value,
                          const ParamValueScope& scope) {
  if (target.kind == Kind::kUnknown || value.kind == Kind::kUnknown)
    return true;
  switch (target.kind) {
    case Kind::kNumber:
      return IsNumeric(value.kind) || value.kind == Kind::kPattern;
    case Kind::kString:
      return value.kind == Kind::kString || value.kind == Kind::kStringLiteral;
    case Kind::kEnum:
      return value.kind == Kind::kEnum && SameIdentity(target, value);
    case Kind::kArray:
      return value.kind == Kind::kPattern ||
             (value.kind == Kind::kArray &&
              ArraysAssignable(target, value, scope.tables.typedefs));
    case Kind::kStructure:
      return value.kind == Kind::kPattern ||
             (value.kind == Kind::kStructure && SameIdentity(target, value));
    default:
      return value.kind == Kind::kNull ||
             (value.kind == Kind::kClass &&
              IsClassDerivedFrom(value.class_name, target.class_name,
                                 scope.unit));
  }
}

}  // namespace delta
