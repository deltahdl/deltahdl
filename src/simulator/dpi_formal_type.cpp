#include "simulator/dpi_formal_type.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

bool IsVectorKind(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
         kind == DataTypeKind::kReg;
}

bool HasPackedDimension(const DataType& type) {
  return type.packed_dim_left != nullptr || !type.extra_packed_dims.empty() ||
         type.has_unsized_packed_dim;
}

// The key RtlirDesign's type tables record a typedef name under: the bare name
// for a module's or an imported one, "Scope::name" for a package's or a
// class's.
std::string TypeKey(const DataType& type) {
  if (type.scope_name.empty()) return std::string(type.type_name);
  return std::string(type.scope_name) + "::" + std::string(type.type_name);
}

// §H.7.4: a packed struct or union crosses as the one-dimensional packed array
// of its width, 4-state where any member is.
DpiCrossingType PackedAggregate(const DataType& type, uint32_t width) {
  DpiCrossingType out;
  out.kind = Is4stateType(type, TypedefMap{}) ? DataTypeKind::kLogic
                                              : DataTypeKind::kBit;
  out.width = width;
  out.is_unsigned = !type.is_signed;
  out.is_packed_array = true;
  return out;
}

// A type whose kind is its own, written without a typedef name.
DpiCrossingType Written(const DataType& type) {
  DpiCrossingType out;
  out.kind = type.kind;
  out.is_unsigned = !type.is_signed;
  out.type_name = type.type_name;
  if (IsVectorKind(type.kind)) {
    out.width = EvalTypeWidth(type);
    out.is_packed_array = HasPackedDimension(type);
  }
  return out;
}

// §H.7.3: an enumeration crosses as its base type, int where none is written.
DpiCrossingType EnumBase(const DataType& type, const RtlirDesign& design) {
  DataType base;
  if (type.enum_base_kind == DataTypeKind::kImplicit) {
    base.kind = DataTypeKind::kInt;
    base.is_signed = true;
    return Written(base);
  }
  base.kind = type.enum_base_kind;
  base.type_name = type.enum_base_name;
  base.is_signed = type.is_signed;
  base.packed_dim_left = type.packed_dim_left;
  base.packed_dim_right = type.packed_dim_right;
  return DpiCrossingTypeOf(base, design);
}

// The entry `map` records under `key`, or null where it records none.
template <typename Value>
const Value* Find(const std::unordered_map<std::string_view, Value>& map,
                  std::string_view key) {
  auto it = map.find(key);
  return it == map.end() ? nullptr : &it->second;
}

// A typedef name standing for a type of kind `kind` that is no enumeration
// and no packed aggregate, recorded under `key`: its width and signedness the
// design's tables give.
DpiCrossingType NamedOfKind(DataTypeKind kind, const DataType& type,
                            const std::string& key, const RtlirDesign& design) {
  const auto* width = Find(design.type_widths, key);
  const auto* is_signed = Find(design.type_signed, key);
  DpiCrossingType out;
  out.kind = kind;
  out.is_unsigned = is_signed == nullptr || !*is_signed;
  out.type_name = type.type_name;
  if (IsVectorKind(kind)) {
    out.width = width == nullptr ? 0 : *width;
    out.is_packed_array = design.type_ranges.contains(key) || out.width > 1;
  }
  return out;
}

// §6.18: a typedef name crosses as the type it stands for.
DpiCrossingType Named(const DataType& type, const RtlirDesign& design) {
  const std::string kKey = TypeKey(type);
  const auto* kind = Find(design.type_kinds, kKey);
  if (kind == nullptr) return Written(type);
  if (*kind == DataTypeKind::kEnum) {
    const auto* decl = Find(design.type_enums, kKey);
    if (decl != nullptr && *decl != nullptr) return EnumBase(**decl, design);
  }
  if (*kind == DataTypeKind::kStruct || *kind == DataTypeKind::kUnion) {
    const auto* layout = Find(design.type_layouts, kKey);
    const auto* width = Find(design.type_widths, kKey);
    if (layout != nullptr && *layout != nullptr && (*layout)->is_packed) {
      return PackedAggregate(**layout, width == nullptr ? 0 : *width);
    }
  }
  return NamedOfKind(*kind, type, kKey, design);
}

// One unpacked dimension a declaration wrote, as its lower and upper bound;
// none where it is open or a bound does not fold. §7.4.2 writes `[N]` for the
// range [0:N-1].
std::optional<SvActualDimension> SizedDimension(const Expr* dim) {
  if (dim == nullptr) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    std::optional<int64_t> left = ConstEvalInt(dim->lhs);
    std::optional<int64_t> right = ConstEvalInt(dim->rhs);
    if (!left || !right) return std::nullopt;
    return SvActualDimension{static_cast<int32_t>(std::min(*left, *right)),
                             static_cast<int32_t>(std::max(*left, *right))};
  }
  std::optional<int64_t> size = ConstEvalInt(dim);
  if (!size || *size <= 0) return std::nullopt;
  return SvActualDimension{0, static_cast<int32_t>(*size - 1)};
}

}  // namespace

DpiCrossingType DpiCrossingTypeOf(const DataType& declared,
                                  const RtlirDesign& design) {
  switch (declared.kind) {
    case DataTypeKind::kNamed:
      return Named(declared, design);
    case DataTypeKind::kEnum:
      return EnumBase(declared, design);
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      if (declared.is_packed) {
        return PackedAggregate(declared, EvalTypeWidth(declared, TypedefMap{}));
      }
      return Written(declared);
    default:
      return Written(declared);
  }
}

std::vector<SvActualDimension> DpiSizedUnpackedDimensions(
    const std::vector<Expr*>& dims) {
  std::vector<SvActualDimension> sized;
  for (const Expr* dim : dims) {
    std::optional<SvActualDimension> folded = SizedDimension(dim);
    if (!folded) return {};
    sized.push_back(*folded);
  }
  return sized;
}

namespace {

// A member of an unpacked struct or union, as the type its declaration names.
DataType MemberType(const StructMember& member) {
  if (member.nested_type != nullptr) return *member.nested_type;
  DataType type;
  type.kind = member.type_kind;
  type.is_signed = member.is_signed;
  type.packed_dim_left = member.packed_dim_left;
  type.packed_dim_right = member.packed_dim_right;
  type.extra_packed_dims = member.extra_packed_dims;
  type.type_name = member.type_name;
  type.scope_name = member.scope_name;
  return type;
}

// The declaration of the unpacked struct or union `type` names or is, typedef
// names followed to it; null where none is found.
const DataType* AggregateDeclaration(const DataType& type,
                                     const SimContext& ctx) {
  const DataType* decl = &type;
  for (size_t hops = 0; decl != nullptr && decl->kind == DataTypeKind::kNamed &&
                        hops <= ctx.TypeDeclarationCount();
       ++hops) {
    decl = ctx.FindTypeDeclaration(TypeKey(*decl));
  }
  return decl != nullptr && !decl->is_packed && !decl->struct_members.empty()
             ? decl
             : nullptr;
}

// Sets `formal`, written as `type` with the unpacked dimensions `unpacked`, to
// what it crosses as: its type, its sized dimensions and, for an unpacked
// struct or union, each member as a formal of its own (§H.7.8).
void ResolveFormal(DpiArg& formal, const DataType& type,
                   const std::vector<Expr*>& unpacked,
                   const RtlirDesign& design, const SimContext& ctx) {
  formal.has_unpacked_dimensions = !unpacked.empty();
  formal.unpacked_dims = DpiSizedUnpackedDimensions(unpacked);
  formal.is_open_array =
      std::find(unpacked.begin(), unpacked.end(), nullptr) != unpacked.end();
  DpiCrossingType crossing = DpiCrossingTypeOf(type, design);
  // A name the design's tables do not resolve may still stand for an
  // unpacked struct or union the run records the declaration of.
  const DataType* decl = crossing.kind == DataTypeKind::kStruct ||
                                 crossing.kind == DataTypeKind::kUnion ||
                                 crossing.kind == DataTypeKind::kNamed
                             ? AggregateDeclaration(type, ctx)
                             : nullptr;
  if (decl != nullptr) crossing.kind = decl->kind;
  formal.type = crossing.kind;
  formal.width = crossing.width;
  formal.is_unsigned = crossing.is_unsigned;
  formal.is_packed_array = crossing.is_packed_array;
  formal.type_name = crossing.type_name;
  formal.members.clear();
  if (decl == nullptr) return;
  for (const StructMember& member : decl->struct_members) {
    DpiArg resolved;
    resolved.name = member.name;
    resolved.direction = formal.direction;
    ResolveFormal(resolved, MemberType(member), member.unpacked_dims, design,
                  ctx);
    formal.members.push_back(std::move(resolved));
  }
}

}  // namespace

void ResolveDpiFormalTypes(DpiRuntime& dpi, const RtlirDesign& design,
                           const SimContext& ctx) {
  for (DpiRtFunction& import : dpi.Imports()) {
    for (DpiArg& formal : import.args) {
      if (formal.declaration == nullptr) continue;
      ResolveFormal(formal, formal.declaration->data_type,
                    formal.declaration->unpacked_dims, design, ctx);
    }
  }
}

}  // namespace delta
