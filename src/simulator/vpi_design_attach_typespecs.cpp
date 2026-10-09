#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// The typespecs one scope declares, by typedef name.
using TypespecsByName = std::unordered_map<std::string_view, VpiObject*>;

// What making one scope's typespecs reads: the scope object they hang from,
// the enumerations the run resolved under each typedef name, and the model to
// build in.
struct ScopeTypespecs {
  VpiObject* scope;
  const std::unordered_map<std::string_view, std::vector<RtlirEnumMember>>*
      enums;
  const VpiAttachBuild& build;
};

// §37.25: an enum const of `typespec`, named after the member and holding its
// value.
void MakeEnumConst(VpiObject* typespec, const RtlirEnumMember& member,
                   const VpiAttachBuild& build) {
  VpiObject* constant = build.alloc();
  constant->type = vpiEnumConst;
  constant->name = build.keep(std::string(member.name));
  constant->parent = typespec;
  auto* storage = build.arena.Create<Variable>();
  storage->value =
      MakeLogic4VecVal(build.arena, 32, static_cast<uint64_t>(member.value));
  constant->var = storage;
  constant->size = 32;
  typespec->children.push_back(constant);
}

// §37.26: a typespec member of `typespec`, named after the member.
void MakeTypespecMember(VpiObject* typespec, const StructMember& member,
                        const VpiAttachBuild& build) {
  VpiObject* typespec_member = build.alloc();
  typespec_member->type = vpiTypespecMember;
  typespec_member->name = build.keep(std::string(member.name));
  typespec_member->parent = typespec;
  typespec->children.push_back(typespec_member);
}

// §37.25 and §37.26: the typespec the typedef `item` declares, named after
// it, with an enum's constants or a struct's or union's members; null for a
// type it draws no typespec for here.
VpiObject* MakeTypespec(const ModuleItem& item, const ScopeTypespecs& at) {
  const DataType& type = item.typedef_type;
  const int kKind = VpiTypespecKind(type.kind);
  if (kKind == 0) return nullptr;
  VpiObject* typespec = at.build.alloc();
  typespec->type = kKind;
  typespec->name = at.build.keep(std::string(item.name));
  typespec->parent = at.scope;
  typespec->full_name = (at.scope != nullptr ? at.scope->full_name + "." : "") +
                        std::string(item.name);
  if (type.kind == DataTypeKind::kEnum && at.enums != nullptr) {
    auto it = at.enums->find(item.name);
    if (it != at.enums->end()) {
      for (const RtlirEnumMember& member : it->second) {
        MakeEnumConst(typespec, member, at.build);
      }
    }
  }
  for (const StructMember& member : type.struct_members) {
    MakeTypespecMember(typespec, member, at.build);
  }
  if (at.scope != nullptr) at.scope->children.push_back(typespec);
  return typespec;
}

// The typespecs of the typedefs among `items`, made under `at.scope`.
TypespecsByName MakeTypespecs(const std::vector<ModuleItem*>& items,
                              const ScopeTypespecs& at) {
  TypespecsByName made;
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    VpiObject* typespec = MakeTypespec(*item, at);
    if (typespec != nullptr) made[item->name] = typespec;
  }
  return made;
}

// The module, interface or program `unit` declares under `name`.
const ModuleDecl* ElementNamed(const CompilationUnit& unit,
                               std::string_view name) {
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      if (decl->name == name) return decl;
    }
  }
  return nullptr;
}

// §37.17: the typespec of the typedef `var` was declared with, its own scope's
// or else the compilation unit's; null where its type names no typedef either
// declares.
VpiObject* DeclaredTypespec(const RtlirVariable& var,
                            const TypespecsByName& local,
                            const TypespecsByName& unit) {
  const DataType* written = var.written_type;
  if (written == nullptr || written->kind != DataTypeKind::kNamed) {
    return nullptr;
  }
  for (const TypespecsByName* scope : {&local, &unit}) {
    auto it = scope->find(written->type_name);
    if (it != scope->end()) return it->second;
  }
  return nullptr;
}

}  // namespace

VpiObjectMap AttachTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiAttachBuild& build) {
  // §37.25, §37.26 and §37.85 detail 5: each typedef a scope declares is a
  // typespec named after it, an enum's with its constants and a struct's or
  // union's with its members; and §37.17 relates a variable declared with one
  // to it. No typespec of any kind was made, so vpiTypedef reached none and a
  // variable's vpiTypespec was null.
  if (design->compilation_unit == nullptr) return {};
  const CompilationUnit& unit = *design->compilation_unit;
  auto unit_scope = objects.find("$unit");
  const TypespecsByName kUnit =
      MakeTypespecs(unit.cu_items,
                    {unit_scope == objects.end() ? nullptr : unit_scope->second,
                     nullptr, build});
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        const ModuleDecl* decl = ElementNamed(unit, mod->name);
        if (decl == nullptr) return;
        const TypespecsByName kLocal =
            MakeTypespecs(decl->items, {scope, &mod->enum_types, build});
        for (const RtlirVariable& var : mod->variables) {
          VpiObject* typespec = DeclaredTypespec(var, kLocal, kUnit);
          VpiObject* obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (typespec != nullptr && obj != nullptr) {
            obj->children.push_back(typespec);
          }
        }
      });
  return kUnit;
}

}  // namespace delta
