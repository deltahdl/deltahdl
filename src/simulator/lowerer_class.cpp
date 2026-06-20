#include "simulator/lowerer.h"

#include <string>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static void AddOrUpdateVTableEntry(ClassTypeInfo* info,
                                   const ClassMember* member) {
  int idx = info->FindVTableIndex(member->method->name);
  auto* method_ptr = member->is_pure_virtual ? nullptr : member->method;
  if (idx >= 0) {
    info->vtable[static_cast<size_t>(idx)].method = method_ptr;
    info->vtable[static_cast<size_t>(idx)].owner = info;
  } else {
    info->vtable.push_back({member->method->name, method_ptr, info});
  }
}

static void BuildVTable(ClassTypeInfo* info, const ClassDecl* cls) {
  if (info->parent) info->vtable = info->parent->vtable;
  for (const auto* iface : info->extended_interfaces) {
    if (!iface) continue;
    for (const auto& entry : iface->vtable) {
      bool found = false;
      for (const auto& existing : info->vtable) {
        if (existing.method_name == entry.method_name) {
          found = true;
          break;
        }
      }
      if (!found) info->vtable.push_back(entry);
    }
  }
  for (auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kMethod || !member->method) continue;

    // A method that redeclares an inherited virtual entry overrides it and
    // stays virtual even when the 'virtual' keyword is omitted (8.20). A
    // ':initial' method is excluded: it explicitly does not act as a virtual
    // override, so it never updates an inherited slot.
    bool overrides_inherited_virtual =
        !member->method->is_method_initial &&
        info->FindVTableIndex(member->method->name) >= 0;
    if (!member->is_virtual && !member->is_pure_virtual &&
        !member->method->is_method_extends && !overrides_inherited_virtual)
      continue;
    AddOrUpdateVTableEntry(info, member);
  }
}

static void InitStaticProperties(ClassTypeInfo* info, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& p : info->properties) {
    if (p.is_static) {
      if (p.init_expr) {
        info->static_properties[std::string(p.name)] =
            EvalExpr(p.init_expr, ctx, arena);
      } else {
        info->static_properties[std::string(p.name)] =
            MakeLogic4VecVal(arena, p.width, 0);
      }
    }
  }
}

void Lowerer::LowerClassDecl(const ClassDecl* cls) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->is_abstract = cls->is_virtual;
  info->is_interface = cls->is_interface;

  if (!cls->base_class.empty())
    info->parent = ctx_.FindClassType(cls->base_class);
  for (const auto& ref : cls->extends_interfaces) {
    auto* iface = ctx_.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (const auto& ref : cls->implements_types) {
    auto* iface = ctx_.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty) {
      uint32_t w = EvalTypeWidth(member->data_type, {});
      if (w == 0) w = 32;
      info->properties.push_back({member->name, w, member->is_static,
                                  member->is_local, member->is_protected,
                                  member->is_const, member->init_expr});
    } else if (member->kind == ClassMemberKind::kMethod && member->method) {
      std::string name(member->method->name);
      info->methods[name] = member->method;
    }
  }
  BuildVTable(info, cls);
  InitStaticProperties(info, ctx_, arena_);

  for (const auto& [pname, pexpr] : cls->params) {
    info->properties.push_back({pname, 32, false});
    if (pexpr) {
      info->static_properties[std::string(pname)] =
          EvalExpr(pexpr, ctx_, arena_);
    } else {
      info->static_properties[std::string(pname)] =
          MakeLogic4VecVal(arena_, 32, 0);
    }
  }

  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kTypedef || !member->typedef_item)
      continue;
    const auto& enum_members = member->typedef_item->typedef_type.enum_members;
    int64_t next_val = 0;
    for (const auto& em : enum_members) {
      if (em.value) next_val = static_cast<int64_t>(em.value->int_val);
      info->enum_members[std::string(em.name)] =
          static_cast<uint64_t>(next_val);
      ++next_val;
    }
  }

  if (cls->is_interface) {
    auto inherit_from = [&](const ClassTypeInfo* src) {
      for (const auto& [k, v] : src->static_properties) {
        if (info->static_properties.find(k) == info->static_properties.end())
          info->static_properties[k] = v;
      }
      for (const auto& [k, v] : src->enum_members) {
        if (info->enum_members.find(k) == info->enum_members.end())
          info->enum_members[k] = v;
      }
    };
    if (info->parent && info->parent->is_interface) inherit_from(info->parent);
    for (const auto* iface : info->extended_interfaces) inherit_from(iface);
  }
  ctx_.RegisterClassType(cls->name, info);

  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class) {
      auto qualified = std::string(cls->name) +
                       "::" + std::string(member->nested_class->name);
      auto* nested_info = arena_.Create<ClassTypeInfo>();
      nested_info->name = *arena_.Create<std::string>(std::move(qualified));
      nested_info->decl = member->nested_class;
      nested_info->is_abstract = member->nested_class->is_virtual;
      nested_info->is_interface = member->nested_class->is_interface;
      if (!member->nested_class->base_class.empty())
        nested_info->parent =
            ctx_.FindClassType(member->nested_class->base_class);
      for (auto* m : member->nested_class->members) {
        if (m->kind == ClassMemberKind::kProperty) {
          uint32_t w = EvalTypeWidth(m->data_type, {});
          if (w == 0) w = 32;
          nested_info->properties.push_back({m->name, w, m->is_static,
                                             m->is_local, m->is_protected,
                                             m->is_const, m->init_expr});
        } else if (m->kind == ClassMemberKind::kMethod && m->method) {
          nested_info->methods[std::string(m->method->name)] = m->method;
        }
      }
      InitStaticProperties(nested_info, ctx_, arena_);
      ctx_.RegisterClassType(nested_info->name, nested_info);
    }
  }
}

}  // namespace delta
