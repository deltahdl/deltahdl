#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static std::string_view NestedLayoutName(const StructMember& m, Arena& arena) {
  if (m.scope_name.empty()) return m.type_name;
  return *arena.Create<std::string>(std::string(m.scope_name) +
                                    "::" + std::string(m.type_name));
}

static void RecordDeclRange(const StructMember& m, StructFieldInfo& fi) {
  if (!m.extra_packed_dims.empty() || m.packed_dim_left == nullptr ||
      m.packed_dim_right == nullptr)
    return;
  auto left = ConstEvalInt(m.packed_dim_left);
  auto right = ConstEvalInt(m.packed_dim_right);
  if (left && right) fi.decl_range = PackedRange{*left, *right};
}

static uint32_t ElementWidth(const StructMember& m, SimContext& ctx) {
  bool unresolved_name = m.nested_type == nullptr && m.resolved_width == 0 &&
                         m.type_kind == DataTypeKind::kNamed;
  return unresolved_name ? NamedMemberWidth(m, ctx) : EvalStructMemberWidth(m);
}

static uint32_t StorageWidth(const StructMember& m, SimContext& ctx) {
  if (IsDynamicArrayMember(m)) return kDynamicMemberHandleWidth;
  return ElementWidth(m, ctx) * UnpackedMemberCount(m);
}

static void RecordOuterPackedDim(const StructMember& m, StructFieldInfo& fi,
                                 SimContext& ctx) {
  bool has_element = !m.extra_packed_dims.empty() ||
                     m.type_kind == DataTypeKind::kNamed ||
                     m.nested_type != nullptr;
  if (!has_element || m.packed_dim_left == nullptr ||
      m.packed_dim_right == nullptr)
    return;
  auto left = ConstEvalInt(m.packed_dim_left);
  auto right = ConstEvalInt(m.packed_dim_right);
  if (!left || !right) return;
  auto size = static_cast<uint32_t>(std::abs(*left - *right) + 1);
  uint32_t width = ElementWidth(m, ctx);
  if (size == 0 || width % size != 0) return;
  fi.packed_left = *left;
  fi.packed_right = *right;
  fi.packed_elem_width = width / size;
  if (!m.extra_packed_dims.empty()) fi.inner_packed_dims = &m.extra_packed_dims;
}

static uint32_t MembersWidth(const DataType& dtype, SimContext& ctx) {
  return CombinedMemberWidth(
      dtype, [&ctx](const StructMember& m) { return StorageWidth(m, ctx); });
}

static uint32_t NestedElementWidth(const StructMember& m, SimContext& ctx) {
  return m.nested_type->packed_dim_left != nullptr
             ? MembersWidth(*m.nested_type, ctx)
             : EvalStructMemberWidth(m);
}

static StructTypeInfo* BuildStructTypeInfo(const DataType* dtype,
                                           uint32_t total_width,
                                           std::string_view type_name,
                                           SimContext& ctx, Arena& arena) {
  auto* info = arena.Create<StructTypeInfo>();
  info->type_name = type_name;
  info->is_packed = dtype->is_packed;
  info->is_union = (dtype->kind == DataTypeKind::kUnion);
  info->is_soft = dtype->is_soft;
  info->total_width = total_width;

  uint32_t offset = total_width;
  for (const auto& m : dtype->struct_members) {
    uint32_t fw = StorageWidth(m, ctx);
    uint32_t field_off = 0;
    if (!info->is_union) {
      offset -= fw;
      field_off = offset;
    }
    StructFieldInfo fi{m.name, field_off, fw, m.type_kind};
    fi.is_signed = m.is_signed;
    fi.is_rand = m.is_rand;
    fi.is_randc = m.is_randc;
    if (IsDynamicArrayMember(m)) {
      fi.is_dynamic = true;
      fi.dyn_elem_width = ElementWidth(m, ctx);
      fi.dyn_max_size = QueueDimMaxSize(m.unpacked_dims.front());
    }
    if (!m.type_name.empty()) fi.type_name = NestedLayoutName(m, arena);
    if (UnpackedMemberBounds(m, &fi.elem_left, &fi.elem_right))
      fi.elem_count = UnpackedMemberCount(m);
    if (!m.unpacked_dims.empty()) fi.unpacked_dims = &m.unpacked_dims;
    fi.default_expr = m.init_expr;
    RecordOuterPackedDim(m, fi, ctx);
    RecordDeclRange(m, fi);
    if (m.nested_type && !m.nested_type->struct_members.empty()) {
      fi.nested = BuildStructTypeInfo(m.nested_type, NestedElementWidth(m, ctx),
                                      NestedLayoutName(m, arena), ctx, arena);
    }
    info->fields.push_back(fi);
  }
  return info;
}

static uint32_t AggregateTypeWidth(const DataType* dtype, SimContext& ctx) {
  uint32_t total = 0;
  for (const auto& m : dtype->struct_members) {
    uint32_t w = StorageWidth(m, ctx);
    if (dtype->kind == DataTypeKind::kUnion) {
      total = std::max(total, w);
    } else {
      total += w;
    }
  }
  return total;
}

void RegisterTypeLayout(std::string_view name, const DataType* dtype,
                        SimContext& ctx, Arena& arena) {
  if (dtype == nullptr || dtype->struct_members.empty()) return;
  auto* info = BuildStructTypeInfo(dtype, AggregateTypeWidth(dtype, ctx), name,
                                   ctx, arena);
  ctx.RegisterStructType(name, *info);
}

void RegisterDesignTypeLayouts(const RtlirDesign* design, SimContext& ctx,
                               Arena& arena) {
  for (const auto& [name, dtype] : design->type_layouts)
    RegisterTypeLayout(name, dtype, ctx, arena);
  RegisterPackageClassVariables(design, ctx, arena);
}

EnumMemberInfo EnumMemberInfoOf(const RtlirEnumMember& m, uint32_t width,
                                SimContext& ctx, Arena& arena) {
  EnumMemberInfo info{m.name, static_cast<uint64_t>(m.value)};
  if (m.xz_value == nullptr || width == 0) return info;
  Logic4Vec v = EvalExpr(m.xz_value, ctx, arena, width);
  if (v.fills_width) v = FillUnbasedUnsized(v, width, arena);
  if (v.nwords == 0) return info;
  uint64_t mask = width >= 64 ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  info.value = v.words[0].aval & mask;
  info.xz = v.words[0].bval & mask;
  return info;
}

void RegisterDesignEnumTypes(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena) {
  for (const auto& [name, dtype] : design->type_enums) {
    if (dtype == nullptr || name.find("::") == std::string_view::npos ||
        ctx.FindEnumType(name) != nullptr) {
      continue;
    }
    EnumTypeInfo info;
    info.type_name = name;
    info.width = EvalTypeWidth(EnumArrayElement(*dtype));
    info.is_4state = Is4stateType(*dtype, TypedefMap{});
    info.is_signed = IsSignedType(*dtype, TypedefMap{});
    for (const RtlirEnumMember& m :
         FoldEnumMembers(dtype->enum_members, design->unit_constants, arena)) {
      info.members.push_back(EnumMemberInfoOf(m, info.width, ctx, arena));
    }
    ctx.RegisterEnumType(name, info);
  }
}

bool HasFourStateMember(const StructTypeInfo& info) {
  return std::any_of(
      info.fields.begin(), info.fields.end(), [](const StructFieldInfo& f) {
        return f.nested != nullptr ? HasFourStateMember(*f.nested)
                                   : Is4stateType(f.type_kind);
      });
}

static void SetFourStateMembersToX(Logic4Vec& value, const StructTypeInfo& info,
                                   uint32_t base, Arena& arena) {
  for (const auto& f : info.fields) {
    if (f.nested != nullptr) {
      SetFourStateMembersToX(value, *f.nested, base + f.bit_offset, arena);
    } else if (Is4stateType(f.type_kind)) {
      DepositBitField(value, base + f.bit_offset, MakeAllX(arena, f.width),
                      f.width);
    }
  }
}

void MarkUnpackedStructStorage(std::string_view name, Variable* v,
                               bool fill_defaults, SimContext& ctx) {
  const StructTypeInfo* info = ctx.GetVariableStructType(name);
  if (info == nullptr || info->is_packed || !HasFourStateMember(*info)) return;
  v->is_4state = true;
  if (info->is_union) return;
  if (fill_defaults) SetFourStateMembersToX(v->value, *info, 0, ctx.GetArena());
}

void RegisterAggregateLayout(std::string_view name, const DataType* dtype,
                             uint32_t width, SimContext& ctx, Arena& arena) {
  if (!dtype || dtype->struct_members.empty()) return;
  if (dtype->packed_dim_left != nullptr) width = MembersWidth(*dtype, ctx);
  auto* info = BuildStructTypeInfo(dtype, width, name, ctx, arena);
  ctx.RegisterStructType(name, *info);
  ctx.SetVariableStructType(name, name);
}

const StructTypeInfo* InlineAggregateLayout(const DataType& written,
                                            SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  auto* key = arena.Create<std::string>(
      std::format("@{:x}", reinterpret_cast<uintptr_t>(&written)));
  RegisterAggregateLayout(*key, &written, MembersWidth(written, ctx), ctx,
                          arena);
  return ctx.FindStructType(*key);
}

}  // namespace delta
