#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// §26.3 (printed page 808) and §8.23: the name a nested member's layout is
// registered under is the member's type as written, `q::pair_t` for `q::pair_t
// p`, the "scope::name" spelling the design's type layouts key that typedef
// by; the bare `pair_t` named another package's same-named typedef, or an
// imported one, in the registered layouts. Arena-owned, as the layout's
// string_view outlives this walk.
static std::string_view NestedLayoutName(const StructMember& m, Arena& arena) {
  if (m.scope_name.empty()) return m.type_name;
  return *arena.Create<std::string>(std::string(m.scope_name) +
                                    "::" + std::string(m.type_name));
}

// §7.4.1: the outermost packed dimension of a member of several, and the width
// of one element of it, the member's width over the dimension's size.
static void RecordOuterPackedDim(const StructMember& m, StructFieldInfo& fi) {
  if (m.extra_packed_dims.empty() || m.packed_dim_left == nullptr ||
      m.packed_dim_right == nullptr)
    return;
  auto left = ConstEvalInt(m.packed_dim_left);
  auto right = ConstEvalInt(m.packed_dim_right);
  if (!left || !right) return;
  auto size = static_cast<uint32_t>(std::abs(*left - *right) + 1);
  uint32_t width = EvalStructMemberWidth(m);
  if (size == 0 || width % size != 0) return;
  fi.packed_left = *left;
  fi.packed_right = *right;
  fi.packed_elem_width = width / size;
}

// Builds the layout of a struct/union DataType: each field's bit offset (within
// its own width frame) and width, recursing into aggregate members so a nested
// member is reachable by its dotted path (§7.2.1). The result is arena-owned so
// the registered top-level copy's nested pointers stay valid.
static StructTypeInfo* BuildStructTypeInfo(const DataType* dtype,
                                           uint32_t total_width,
                                           std::string_view type_name,
                                           Arena& arena) {
  auto* info = arena.Create<StructTypeInfo>();
  info->type_name = type_name;
  info->is_packed = dtype->is_packed;
  info->is_union = (dtype->kind == DataTypeKind::kUnion);
  info->is_soft = dtype->is_soft;
  info->total_width = total_width;

  uint32_t offset = total_width;
  for (const auto& m : dtype->struct_members) {
    uint32_t fw = StructMemberStorageWidth(m);
    uint32_t field_off = 0;
    if (!info->is_union) {
      offset -= fw;
      field_off = offset;
    }
    StructFieldInfo fi{m.name, field_off, fw, m.type_kind};
    // §7.2.1 with §6.22.2 c): the member's signedness as the parser resolved
    // it, the modifier where one was written and the kind's default where
    // none was (ApplyMemberType in parser_aggregate_types.cpp).
    fi.is_signed = m.is_signed;
    // §18.4: the members the type declares random, which a rand variable of
    // an unpacked structure of it has randomized.
    fi.is_rand = m.is_rand;
    fi.is_randc = m.is_randc;
    // §7.2 with §7.5: a dynamic array member holds a handle to its elements,
    // each EvalStructMemberWidth bits wide.
    if (IsDynamicArrayMember(m)) {
      fi.is_dynamic = true;
      fi.dyn_elem_width = EvalStructMemberWidth(m);
    }
    if (!m.type_name.empty()) fi.type_name = NestedLayoutName(m, arena);
    if (UnpackedMemberBounds(m, &fi.elem_left, &fi.elem_right))
      fi.elem_count = UnpackedMemberCount(m);
    fi.default_expr = m.init_expr;
    RecordOuterPackedDim(m, fi);
    if (m.nested_type && !m.nested_type->struct_members.empty()) {
      fi.nested = BuildStructTypeInfo(m.nested_type, EvalStructMemberWidth(m),
                                      NestedLayoutName(m, arena), arena);
    }
    info->fields.push_back(fi);
  }
  return info;
}

// §7.2.1: the bit count of an aggregate declaration, which is the frame its
// members' offsets are measured in. A packed struct is as wide as its members
// together and a packed union as wide as its widest, which is the same sum
// BuildStructTypeInfo walks below.
static uint32_t AggregateTypeWidth(const DataType* dtype) {
  uint32_t total = 0;
  for (const auto& m : dtype->struct_members) {
    uint32_t w = StructMemberStorageWidth(m);
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
  auto* info =
      BuildStructTypeInfo(dtype, AggregateTypeWidth(dtype), name, arena);
  ctx.RegisterStructType(name, *info);
}

void RegisterDesignTypeLayouts(const RtlirDesign* design, SimContext& ctx,
                               Arena& arena) {
  for (const auto& [name, dtype] : design->type_layouts)
    RegisterTypeLayout(name, dtype, ctx, arena);
  // §26.3 with §8.4: the class a package variable is declared with is the
  // other declared-type fact no module's lowering records, so it is recorded
  // beside the layouts.
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

// §6.19.5 with §6.18: the enumeration behind each typedef name the design
// records (RtlirDesign::type_enums), registered under the typedef's key, so
// that a value declared with a class's "C::name" (§8.23) or a package's
// "P::name" (§26.3) has members for the methods to walk. A bare name is left
// to the module that declares or imports it: Lowerer::RegisterEnumTypes folds
// that one against the module's own constants, which a member value may name,
// while the design's copy folds against the compilation unit's alone.
void RegisterDesignEnumTypes(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena) {
  for (const auto& [name, dtype] : design->type_enums) {
    if (dtype == nullptr || name.find("::") == std::string_view::npos ||
        ctx.FindEnumType(name) != nullptr) {
      continue;
    }
    EnumTypeInfo info;
    info.type_name = name;
    info.width = EvalTypeWidth(*dtype);
    info.is_4state = Is4stateType(*dtype, TypedefMap{});
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

// §6.8, Table 6-7: each 4-state member's window of `value`, the structure
// `info` lays out from bit `base`, set to x.
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
  // §7.3: an unpacked union starts at its first member's default, which the
  // variable was already given by that member's type; only its storage keeps
  // x and z for the 4-state members a later write names (§7.3.2).
  if (info->is_union) return;
  if (fill_defaults) SetFourStateMembersToX(v->value, *info, 0, ctx.GetArena());
}

void RegisterAggregateLayout(std::string_view name, const DataType* dtype,
                             uint32_t width, SimContext& ctx, Arena& arena) {
  if (!dtype || dtype->struct_members.empty()) return;
  auto* info = BuildStructTypeInfo(dtype, width, name, arena);
  ctx.RegisterStructType(name, *info);
  ctx.SetVariableStructType(name, name);
}

}  // namespace delta
