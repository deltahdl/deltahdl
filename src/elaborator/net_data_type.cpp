#include "elaborator/net_data_type.h"

#include <array>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/queue_dim.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kMaxTypedefHops = 16;

constexpr std::array<std::string_view, 12> kAssocIndexKeywords = {
    "string", "int",   "integer", "byte", "shortint", "longint",
    "bit",    "logic", "reg",     "time", "chandle",  "event"};

}  // namespace

const DataType* FollowTypedefs(const DataType& dtype,
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
  if (dim->kind == ExprKind::kTypeRef) return false;
  if (dim->kind != ExprKind::kIdentifier) {
    const std::string kKey = ScopedTypeKey(dim);
    return tables.typedefs.count(kKey) == 0 &&
           tables.class_names.count(kKey) == 0;
  }
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

bool TypedefDimsAreFixedSize(const DataType& dtype,
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

std::string NamedTypeKey(std::string_view scope, std::string_view name) {
  if (scope.empty()) return std::string(name);
  return std::string(scope) + "::" + std::string(name);
}

std::string NamedTypeKey(const DataType& type) {
  return NamedTypeKey(type.scope_name, type.type_name);
}

static bool NamesStdClass(const DataType& type) {
  if (type.scope_name != "std") return false;
  std::optional<StdPackageMember> member =
      StdPackageMemberNamed(type.type_name);
  return member.has_value() &&
         KindOfStdPackageMember(*member) == StdPackageMemberKind::kClass;
}

bool IsLegalNettypeDataType(const DataType& dtype,
                            const TypeShapeTables& tables) {
  const DataType* type = &dtype;
  for (int hops = 0; type != nullptr && hops < kMaxTypedefHops; ++hops) {
    if (type->kind != DataTypeKind::kNamed)
      return IsLegalNettypeElement(*type, tables);
    const std::string kKey = NamedTypeKey(*type);
    if (tables.class_names.count(kKey) != 0 || NamesStdClass(*type))
      return false;
    auto dims = tables.typedef_dims.find(kKey);
    if (dims != tables.typedef_dims.end() &&
        !AllFixedSize(dims->second, tables))
      return false;
    auto it = tables.typedefs.find(kKey);
    type = it != tables.typedefs.end() ? &it->second : nullptr;
  }
  return true;
}

static bool NamesCovergroup(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::function<bool(std::string_view)>& names_covergroup) {
  if (!names_covergroup) return false;
  std::vector<std::string_view> names;
  if (FollowTypedefs(dtype, typedefs, names) != nullptr || names.empty())
    return false;
  return names_covergroup(names.back());
}

void ReportIllegalNettypeDataType(
    const ModuleItem& nettype, const TypeShapeTables& tables, DiagEngine& diag,
    const std::function<bool(std::string_view)>& names_covergroup) {
  if (IsLegalNettypeDataType(nettype.typedef_type, tables) &&
      !NamesCovergroup(nettype.typedef_type, tables.typedefs, names_covergroup))
    return;
  diag.Error(nettype.loc,
             std::format("data type of user-defined nettype '{}' is not a "
                         "legal nettype data type",
                         nettype.name),
             Subclause("6.6.7"));
}

}  // namespace delta
