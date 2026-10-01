#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// The layout of the structure the property `name` of `level` holds, null
// where it holds none.
const StructTypeInfo* PropertyLayout(std::string_view name,
                                     const ClassTypeInfo* level,
                                     SimContext& ctx) {
  for (const auto& p : level->properties) {
    if (p.name != name) continue;
    return p.type_name.empty() ? nullptr : ctx.FindStructType(p.type_name);
  }
  return nullptr;
}

}  // namespace

bool AddRandStructMembers(const ClassMember* m, const ClassTypeInfo* level,
                          SimContext& ctx, std::vector<RandInfo>& out) {
  if (m->data_type.kind != DataTypeKind::kNamed) return false;
  const StructTypeInfo* layout = PropertyLayout(m->name, level, ctx);
  if (layout == nullptr || layout->is_packed || layout->is_union) return false;
  for (const StructFieldInfo& field : layout->fields) {
    // A member of no integral layout -- an array, a nested aggregate -- is
    // no variable of the structure's bits.
    if (!(field.is_rand || field.is_randc) || field.width == 0 ||
        field.elem_count != 0 || field.nested != nullptr) {
      continue;
    }
    RandInfo info;
    info.name = std::string(m->name) + "." + std::string(field.name);
    info.level = level;
    info.var.name = info.name;
    info.var.qualifier =
        field.is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
    info.var.width = field.width;
    info.var.is_signed = field.is_signed;
    info.var.BindDomainToDeclaredRange();
    info.struct_base = std::string(m->name);
    info.struct_offset = field.bit_offset;
    out.push_back(std::move(info));
  }
  return true;
}

}  // namespace delta
