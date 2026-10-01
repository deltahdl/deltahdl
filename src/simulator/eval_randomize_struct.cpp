#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// The members the typedef `name` declares, the class chain from `level`
// searched for it; null where no class of the chain declares a structure of
// the name.
const std::vector<StructMember>* TypedefStructMembers(
    std::string_view name, const ClassTypeInfo* level) {
  for (const auto* t = level; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kTypedef && m->typedef_item != nullptr &&
          m->typedef_item->name == name &&
          !m->typedef_item->typedef_type.struct_members.empty()) {
        return &m->typedef_item->typedef_type.struct_members;
      }
    }
  }
  return nullptr;
}

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
  const std::vector<StructMember>* members =
      TypedefStructMembers(m->data_type.type_name, level);
  if (members == nullptr) return false;
  for (const StructMember& member : *members) {
    if (!(member.is_rand || member.is_randc)) continue;
    const StructFieldInfo* field = FindStructField(layout, member.name);
    // A member of no integral layout -- an array, a nested aggregate -- is
    // no variable of the structure's bits.
    if (field == nullptr || field->width == 0 || field->elem_count != 0 ||
        field->nested != nullptr || !member.unpacked_dims.empty()) {
      continue;
    }
    RandInfo info;
    info.name = std::string(m->name) + "." + std::string(member.name);
    info.level = level;
    info.var.name = info.name;
    info.var.qualifier =
        member.is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
    info.var.width = field->width;
    info.var.is_signed = field->is_signed;
    info.var.BindDomainToDeclaredRange();
    info.struct_base = std::string(m->name);
    info.struct_offset = field->bit_offset;
    out.push_back(std::move(info));
  }
  return true;
}

}  // namespace delta
