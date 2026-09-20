#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

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
    uint32_t fw = EvalStructMemberWidth(m);
    uint32_t field_off = 0;
    if (!info->is_union) {
      offset -= fw;
      field_off = offset;
    }
    StructFieldInfo fi{m.name, field_off, fw, m.type_kind};
    if (m.nested_type && !m.nested_type->struct_members.empty()) {
      fi.nested = BuildStructTypeInfo(m.nested_type, fw,
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
    uint32_t w = EvalStructMemberWidth(m);
    if (dtype->kind == DataTypeKind::kUnion) {
      total = std::max(total, w);
    } else {
      total += w;
    }
  }
  return total;
}

void RegisterDesignTypeLayouts(const RtlirDesign* design, SimContext& ctx,
                               Arena& arena) {
  for (const auto& [name, dtype] : design->type_layouts) {
    if (dtype == nullptr || dtype->struct_members.empty()) continue;
    auto* info =
        BuildStructTypeInfo(dtype, AggregateTypeWidth(dtype), name, arena);
    ctx.RegisterStructType(name, *info);
  }
  // §26.3 with §8.4: the class a package variable is declared with is the
  // other declared-type fact no module's lowering records, so it is recorded
  // beside the layouts.
  RegisterPackageClassVariables(design, ctx, arena);
}

void RegisterAggregateLayout(std::string_view name, const DataType* dtype,
                             uint32_t width, SimContext& ctx, Arena& arena) {
  if (!dtype || dtype->struct_members.empty()) return;
  auto* info = BuildStructTypeInfo(dtype, width, name, arena);
  ctx.RegisterStructType(name, *info);
  ctx.SetVariableStructType(name, name);

}  // namespace delta
