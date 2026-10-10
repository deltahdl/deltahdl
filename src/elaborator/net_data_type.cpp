#include "elaborator/net_data_type.h"

#include <array>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// A typedef chain longer than this runs in a cycle; no legal source writes one
// this long, so the walk gives up rather than looping.
constexpr int kMaxTypedefHops = 16;

// §7.8 (printed page 160): the index types an associative array may be written
// with as a keyword, which the parser keeps as the dimension's text.
constexpr std::array<std::string_view, 10> kAssocIndexKeywords = {
    "string",  "int", "integer", "byte", "shortint",
    "longint", "bit", "logic",   "reg",  "time"};

}  // namespace

// The type `dtype` stands for once every typedef name it is written with has
// been followed, or null when a name resolves to nothing in `typedefs` or the
// names run in a cycle. Each name followed is appended to `names`, so a caller
// can ask what each one wrote besides the type.
static const DataType* FollowTypedefs(const DataType& dtype,
                                      const TypedefMap& typedefs,
                                      std::vector<std::string_view>& names) {
  const DataType* type = &dtype;
  for (int hops = 0; hops < kMaxTypedefHops; ++hops) {
    if (type->kind != DataTypeKind::kNamed) return type;
    names.push_back(type->type_name);
    auto it = typedefs.find(type->type_name);
    if (it == typedefs.end()) return nullptr;
    type = &it->second;
  }
  return nullptr;
}

bool IsFixedSizeUnpackedDim(const Expr* dim, const TypeShapeTables& tables) {
  if (dim == nullptr) return false;
  if (dim->kind != ExprKind::kIdentifier) return true;
  if (IsQueueDim(dim) || dim->text == "*") return false;
  for (std::string_view keyword : kAssocIndexKeywords) {
    if (dim->text == keyword) return false;
  }
  return tables.typedefs.count(dim->text) == 0 &&
         tables.class_names.count(dim->text) == 0;
}

static bool AllFixedSize(const std::vector<Expr*>& dims,
                         const TypeShapeTables& tables) {
  for (const Expr* dim : dims) {
    if (!IsFixedSizeUnpackedDim(dim, tables)) return false;
  }
  return true;
}

void ValidateNetDeclaratorDims(const std::vector<Expr*>& dims,
                               const TypeShapeTables& tables, DiagEngine& diag,
                               SourceLoc loc) {
  if (AllFixedSize(dims, tables)) return;
  diag.Error(loc, "a net's unpacked dimension must be fixed-size",
             Subclause("6.7"));
}

// Whether every typedef name the chain from `dtype` passes through wrote only
// fixed-size unpacked dimensions.
static bool TypedefDimsAreFixedSize(const DataType& dtype,
                                    const TypeShapeTables& tables) {
  std::vector<std::string_view> names;
  FollowTypedefs(dtype, tables.typedefs, names);
  for (std::string_view name : names) {
    auto dims = tables.typedef_dims.find(name);
    if (dims != tables.typedef_dims.end() &&
        !AllFixedSize(dims->second, tables)) {
      return false;
    }
  }
  return true;
}

void ValidateNetTypedefDims(const DataType& dtype,
                            const TypeShapeTables& tables, DiagEngine& diag,
                            SourceLoc loc) {
  if (TypedefDimsAreFixedSize(dtype, tables)) return;
  diag.Error(loc, "net data type must be a fixed-size array",
             Subclause("6.7.1"));
}

static bool PackedTypeIs4State(const DataType& dtype,
                               const TypedefMap& typedefs);

// §7.2.1 (printed page 145): a member of a packed structure or union is
// 4-state when its own type is, which for a member written through a typedef
// name or as a nested aggregate or enumeration is the type that name or nesting
// stands for. A name the table cannot resolve leaves nothing to judge, and it
// is taken as 4-state so that the net is not rejected over a type it cannot
// see.
static bool PackedMemberIs4State(const StructMember& m,
                                 const TypedefMap& typedefs) {
  if (m.nested_type != nullptr) {
    return PackedTypeIs4State(*m.nested_type, typedefs);
  }
  if (m.type_kind == DataTypeKind::kNamed) {
    const DataType* named = MemberNamedType(m, typedefs);
    return named == nullptr || PackedTypeIs4State(*named, typedefs);
  }
  return Is4stateType(m.type_kind);
}

// §6.7.1 item a with §7.2.1: a packed structure or union is 4-state when any
// member is, an enumeration when its base is, and anything else when its kind
// is a 4-state one.
static bool PackedTypeIs4State(const DataType& dtype,
                               const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* type = FollowTypedefs(dtype, typedefs, names);
  if (type == nullptr) return true;
  if (type->kind == DataTypeKind::kStruct ||
      type->kind == DataTypeKind::kUnion) {
    for (const auto& m : type->struct_members) {
      if (PackedMemberIs4State(m, typedefs)) return true;
    }
    return type->struct_members.empty();
  }
  if (type->kind == DataTypeKind::kEnum) return Is4stateType(*type, typedefs);
  return Is4stateType(type->kind);
}

static bool IsValidNetType(const DataType& dtype, const TypedefMap& typedefs);

// §6.7.1 item b: a member of an unpacked structure or union is valid when its
// own type is a valid net data type, judged through a typedef name or into a
// nested aggregate as the member's own type would be.
static bool IsValidNetMember(const StructMember& m,
                             const TypedefMap& typedefs) {
  if (m.nested_type != nullptr) return IsValidNetType(*m.nested_type, typedefs);
  if (m.type_kind == DataTypeKind::kNamed) {
    const DataType* named = MemberNamedType(m, typedefs);
    return named == nullptr || IsValidNetType(*named, typedefs);
  }
  return Is4stateType(m.type_kind);
}

static bool UnpackedMembersAreValid(const DataType& dtype,
                                    const TypedefMap& typedefs) {
  for (const auto& m : dtype.struct_members) {
    if (!IsValidNetMember(m, typedefs)) return false;
  }
  return true;
}

static bool IsUnpackedAggregate(const DataType& dtype) {
  return (dtype.kind == DataTypeKind::kStruct ||
          dtype.kind == DataTypeKind::kUnion) &&
         !dtype.is_packed && !dtype.is_soft;
}

// §6.7.1 items a and b for one type. A net type keyword standing where the data
// type would (`wire w;`) leaves the data type implicit, which is logic.
static bool IsValidNetType(const DataType& dtype, const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* type = FollowTypedefs(dtype, typedefs, names);
  if (type == nullptr) return true;
  if (IsUnpackedAggregate(*type))
    return UnpackedMembersAreValid(*type, typedefs);
  DataTypeKind k = type->kind;
  if (DataTypeToNetType(k) != NetType::kWire || k == DataTypeKind::kWire) {
    return true;
  }
  return PackedTypeIs4State(*type, typedefs);
}

void ValidateNetDataTypeIs4State(const DataType& dtype,
                                 const TypedefMap& typedefs, DiagEngine& diag,
                                 SourceLoc loc) {
  if (dtype.is_interconnect) return;
  std::vector<std::string_view> names;
  const DataType* type = FollowTypedefs(dtype, typedefs, names);
  if (type == nullptr) return;
  if (IsUnpackedAggregate(*type)) {
    if (!UnpackedMembersAreValid(*type, typedefs)) {
      diag.Error(loc,
                 "unpacked struct/union net member must be a valid net "
                 "data type",
                 Subclause("6.7.1"));
    }
    return;
  }
  if (!IsValidNetType(*type, typedefs)) {
    diag.Error(loc, "net data type must be 4-state", Subclause("6.7.1"));
  }
}

static bool IsLegalNettypeElement(const DataType& type,
                                  const TypeShapeTables& tables);

// §6.6.7 item d: a member of an unpacked structure or union is legal when its
// dimensions are fixed-size and its own type is legal.
static bool IsLegalNettypeMember(const StructMember& m,
                                 const TypeShapeTables& tables) {
  if (!AllFixedSize(m.unpacked_dims, tables)) return false;
  if (m.nested_type != nullptr) {
    return IsLegalNettypeElement(*m.nested_type, tables);
  }
  DataType own;
  own.kind = m.type_kind;
  own.type_name = m.type_name;
  own.scope_name = m.scope_name;
  return IsLegalNettypeDataType(own, tables);
}

// §6.6.7 items a to d for a type no typedef name stands in front of. A packed
// aggregate is integral (item a or b), and real and shortreal are item c; the
// kinds below are none of these.
static bool IsLegalNettypeElement(const DataType& type,
                                  const TypeShapeTables& tables) {
  switch (type.kind) {
    case DataTypeKind::kString:
    case DataTypeKind::kChandle:
    case DataTypeKind::kEvent:
    case DataTypeKind::kVoid:
    case DataTypeKind::kVirtualInterface:
      return false;
    default:
      break;
  }
  if (!IsUnpackedAggregate(type)) return true;
  for (const auto& m : type.struct_members) {
    if (!IsLegalNettypeMember(m, tables)) return false;
  }
  return true;
}

bool IsLegalNettypeDataType(const DataType& dtype,
                            const TypeShapeTables& tables) {
  std::vector<std::string_view> names;
  const DataType* type = FollowTypedefs(dtype, tables.typedefs, names);
  for (std::string_view name : names) {
    if (tables.class_names.count(name) != 0) return false;
  }
  if (!TypedefDimsAreFixedSize(dtype, tables)) return false;
  return type == nullptr || IsLegalNettypeElement(*type, tables);
}

}  // namespace delta
