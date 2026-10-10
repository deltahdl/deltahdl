#include "elaborator/aggregate_shape.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

// §6.18: the type a member is written with when that is more than a keyword: a
// structure, union or enumeration written in place, or the type a typedef name
// stands for once every name in the chain is followed. Null for a keyword type
// and for a name that resolves to nothing, such as a class.
static const DataType* MemberOwnType(const StructMember& m,
                                     const TypedefMap& typedefs) {
  if (m.nested_type != nullptr) return m.nested_type;
  if (m.type_kind != DataTypeKind::kNamed) return nullptr;
  const DataType* named = MemberNamedType(m, typedefs);
  if (named == nullptr) return nullptr;
  std::vector<std::string_view> names;
  return FollowTypedefs(*named, typedefs, names);
}

// The kind of the type a member is written with, through a typedef name. A
// name that resolves to nothing keeps the kind written, `kNamed`.
static DataTypeKind MemberKind(const StructMember& m,
                               const TypedefMap& typedefs) {
  const DataType* own = MemberOwnType(m, typedefs);
  return own != nullptr ? own->kind : m.type_kind;
}

static bool HasUnionMember(const DataType& dtype, const TypedefMap& typedefs) {
  for (const auto& m : dtype.struct_members) {
    if (MemberKind(m, typedefs) == DataTypeKind::kUnion) return true;
  }
  return false;
}

static void CheckPackedStructDefaults(const DataType& dtype, SourceLoc loc,
                                      const AggregateShapeCtx& ctx) {
  if (dtype.kind != DataTypeKind::kStruct || !dtype.is_packed) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr) {
      ctx.diag.Error(loc,
                     "a member of a packed structure cannot carry a default "
                     "value of its own",
                     Subclause("7.2.2"));
      return;
    }
  }
}

static void CheckUnpackedStructWithUnionDefaults(const DataType& dtype,
                                                 SourceLoc loc,
                                                 const AggregateShapeCtx& ctx) {
  if (dtype.kind != DataTypeKind::kStruct || dtype.is_packed) return;
  if (!HasUnionMember(dtype, ctx.tables.typedefs)) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr) {
      ctx.diag.Error(loc,
                     "a member of an unpacked structure that contains a union "
                     "cannot carry a default value of its own",
                     Subclause("7.2.2"));
      return;
    }
  }
}

// §7.2.2: a member default is a constant expression, which per §11.2.1 may
// reference a parameter of the scope the declaration stands in.
static void CheckStructMemberDefaultsConstant(const DataType& dtype,
                                              SourceLoc loc,
                                              const AggregateShapeCtx& ctx) {
  if (ctx.member_default_scope == nullptr) return;
  if (dtype.kind != DataTypeKind::kStruct || dtype.is_packed) return;
  if (HasUnionMember(dtype, ctx.tables.typedefs)) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr &&
        !IsConstantExpr(m.init_expr, *ctx.member_default_scope)) {
      ctx.diag.Error(loc,
                     "struct member default value must be a constant "
                     "expression",
                     Subclause("7.2.2"));
      return;
    }
  }
}

static void CheckVoidMembers(const DataType& dtype, SourceLoc loc,
                             const AggregateShapeCtx& ctx) {
  bool allow_void = (dtype.kind == DataTypeKind::kUnion && dtype.is_tagged);
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && !allow_void) {
      ctx.diag.Error(loc, "void member is only allowed in tagged unions",
                     Subclause("7.2"));
      return;
    }
  }
}

static void CheckRandQualifiers(const DataType& dtype, SourceLoc loc,
                                const AggregateShapeCtx& ctx) {
  bool allow_rand = (dtype.kind == DataTypeKind::kStruct && !dtype.is_packed);
  for (const auto& m : dtype.struct_members) {
    if ((m.is_rand || m.is_randc) && !allow_rand) {
      ctx.diag.Error(loc,
                     "random qualifier is only allowed in unpacked structures",
                     Subclause("7.2"));
      return;
    }
  }
}

static void CheckPackedDimRequiresPackedKeyword(const DataType& dtype,
                                                SourceLoc loc,
                                                const AggregateShapeCtx& ctx) {
  if (!dtype.packed_dim_left) return;
  if (dtype.is_packed || dtype.is_soft) return;
  const char* kw = (dtype.kind == DataTypeKind::kStruct) ? "struct" : "union";
  ctx.diag.Error(
      loc,
      std::format("packed dimension on {} requires the packed keyword", kw),
      Subclause("7.2"));
}

static bool IsLegalPackedMemberType(DataTypeKind kind) {
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
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
    case DataTypeKind::kNamed:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

bool IsUnpackedAggregate(const DataType* type) {
  return type != nullptr &&
         (type->kind == DataTypeKind::kStruct ||
          type->kind == DataTypeKind::kUnion) &&
         !type->is_packed && !type->is_soft;
}

static void CheckPackedStructMemberTypes(const DataType& dtype, SourceLoc loc,
                                         const AggregateShapeCtx& ctx) {
  if (!dtype.is_packed && !dtype.is_soft) return;
  const char* container = (dtype.kind == DataTypeKind::kStruct)
                              ? "packed structure"
                              : "packed union";
  // §7.3.2: a void member is legal in a packed tagged union — it carries no
  // value bits, and in that extreme case only the tag is significant while the
  // remaining bits are undefined (the packed VInt example). A void member
  // elsewhere is already barred by CheckVoidMembers, so it need only be
  // exempted from the packed-member-type check for the tagged-union case.
  bool tagged_union = dtype.kind == DataTypeKind::kUnion && dtype.is_tagged;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && tagged_union) continue;
    const DataType* own = MemberOwnType(m, ctx.tables.typedefs);
    DataTypeKind kind = own != nullptr ? own->kind : m.type_kind;
    // §7.2.1: a structure or union member of a packed one is itself packed,
    // since only packed types are admitted; an unpacked one written in place or
    // through a typedef name is not.
    if (!IsLegalPackedMemberType(kind) || IsUnpackedAggregate(own)) {
      ctx.diag.Error(loc,
                     std::format("type of member '{}' is not allowed in a {}",
                                 m.name, container),
                     Subclause("7.2.1"));
      continue;
    }
    // §7.2.1: only packed data types are permitted as members. A member that
    // carries unpacked dimensions is an unpacked array, which is not a packed
    // type, so it cannot appear in a packed structure or union.
    if (!m.unpacked_dims.empty()) {
      ctx.diag.Error(
          loc,
          std::format("unpacked array member '{}' is not allowed in a {}",
                      m.name, container),
          Subclause("7.2.1"));
    }
  }
}

// §7.5, §7.8 and §7.10: a dynamic array, an associative array and a queue are
// dynamic types, their size changing as the program runs. A member is one when
// any of its unpacked dimensions is not a fixed size.
static bool HasDynamicDimension(const StructMember& m,
                                const TypeShapeTables& tables) {
  for (const Expr* dim : m.unpacked_dims) {
    if (!IsFixedSizeUnpackedDim(dim, tables)) return true;
  }
  return false;
}

// The report an untagged union makes of member `m`, or the empty string when
// the member is one it may hold.
static std::string UntaggedUnionMemberReport(const StructMember& m,
                                             const TypeShapeTables& tables) {
  if (HasDynamicDimension(m, tables)) {
    return std::format(
        "dynamic array, associative array or queue member '{}' can only be "
        "used in tagged unions",
        m.name);
  }
  switch (MemberKind(m, tables.typedefs)) {
    case DataTypeKind::kChandle:
      return "chandle type can only be used in tagged unions";
    case DataTypeKind::kString:
      return "string type can only be used in tagged unions";
    case DataTypeKind::kEvent:
      return "event type can only be used in tagged unions";
    default:
      return {};
  }
}

static void CheckUntaggedUnionMembers(const DataType& dtype, SourceLoc loc,
                                      const AggregateShapeCtx& ctx) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (dtype.is_tagged) return;
  // §7.3.2 carries the obligation this enforces: dynamic and chandle types are
  // allowed in tagged unions and forbidden in untagged ones. §7.3 states the
  // same fact as descriptive prose and states no obligation, so the report
  // names the subclause that does.
  for (const auto& m : dtype.struct_members) {
    std::string report = UntaggedUnionMemberReport(m, ctx.tables);
    if (!report.empty()) {
      ctx.diag.Error(loc, report, Subclause("7.3.2"));
      return;
    }
  }
}

static void CheckVirtualInterfaceInUnion(const DataType& dtype, SourceLoc loc,
                                         const AggregateShapeCtx& ctx) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVirtualInterface) {
      ctx.diag.Error(loc,
                     "virtual interface cannot be used as a member of a union",
                     Subclause("25.9"));
      return;
    }
  }
}

static void CheckPackedUnion(const DataType& dtype, SourceLoc loc,
                             const AggregateShapeCtx& ctx) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.struct_members.empty()) return;
  if (dtype.is_soft || dtype.is_tagged) return;
  const TypedefMap& typedefs = ctx.tables.typedefs;
  uint32_t first_w = EvalStructMemberWidth(dtype.struct_members[0], typedefs);
  for (size_t i = 1; i < dtype.struct_members.size(); ++i) {
    uint32_t w = EvalStructMemberWidth(dtype.struct_members[i], typedefs);
    if (w != first_w) {
      ctx.diag.Error(loc,
                     std::format("packed union member '{}' has width {} but "
                                 "first member '{}' has width {}",
                                 dtype.struct_members[i].name, w,
                                 dtype.struct_members[0].name, first_w),
                     Subclause("7.3.1"));
    }
  }
}

void CheckAggregateShape(const DataType& dtype, SourceLoc loc,
                         const AggregateShapeCtx& ctx) {
  if (dtype.kind != DataTypeKind::kStruct &&
      dtype.kind != DataTypeKind::kUnion) {
    return;
  }
  CheckPackedStructDefaults(dtype, loc, ctx);
  CheckUnpackedStructWithUnionDefaults(dtype, loc, ctx);
  CheckStructMemberDefaultsConstant(dtype, loc, ctx);
  CheckVoidMembers(dtype, loc, ctx);
  CheckRandQualifiers(dtype, loc, ctx);
  CheckPackedDimRequiresPackedKeyword(dtype, loc, ctx);
  CheckPackedStructMemberTypes(dtype, loc, ctx);
  CheckUntaggedUnionMembers(dtype, loc, ctx);
  CheckVirtualInterfaceInUnion(dtype, loc, ctx);
  CheckPackedUnion(dtype, loc, ctx);
  // A structure or union written in place as a member is a type of its own,
  // under the same rules as one written anywhere else.
  for (const auto& m : dtype.struct_members) {
    if (m.nested_type != nullptr) CheckAggregateShape(*m.nested_type, loc, ctx);
  }
}

}  // namespace delta
