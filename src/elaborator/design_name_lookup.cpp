#include "elaborator/design_name_lookup.h"

#include <algorithm>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

const ModuleDecl* ChildInstanceModule(const CompilationUnit* unit,
                                      const ModuleDecl* decl,
                                      std::string_view instance) {
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_name == instance)
      return FindDefinition(unit, item->inst_module);
  }
  return nullptr;
}

}  // namespace

const ModuleDecl* FindDefinition(const CompilationUnit* unit,
                                 std::string_view name) {
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs}) {
    for (const ModuleDecl* decl : *group) {
      if (decl->name == name) return decl;
    }
  }
  return nullptr;
}

const PackageDecl* FindPackage(const CompilationUnit* unit,
                               std::string_view name) {
  for (const PackageDecl* pkg : unit->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

const ModuleDecl* ModuleAlongPath(const CompilationUnit* unit,
                                  const ModuleDecl* decl,
                                  const std::vector<std::string_view>& path) {
  for (size_t i = 1; i + 1 < path.size() && decl != nullptr; ++i) {
    decl = ChildInstanceModule(unit, decl, path[i]);
  }
  return decl;
}

const ModuleItem* SubroutineAmong(const std::vector<ModuleItem*>& items,
                                  std::string_view name) {
  for (const ModuleItem* item : items) {
    bool subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                      item->kind == ModuleItemKind::kTaskDecl ||
                      item->kind == ModuleItemKind::kDpiImport;
    if (subroutine && item->method_class.empty() && item->name == name)
      return item;
  }
  return nullptr;
}

const ClassMember* ClassMemberOf(const ClassDecl* cls, std::string_view name,
                                 ClassMemberKind kind,
                                 const CompilationUnit* unit) {
  std::vector<const ClassDecl*> lineage;
  for (; cls != nullptr && std::ranges::find(lineage, cls) == lineage.end();
       cls = FindBaseClass(cls, unit)) {
    lineage.push_back(cls);
    for (const ClassMember* m : cls->members) {
      if (m->kind == kind && m->name == name) return m;
    }
  }
  return nullptr;
}

const ModuleItem* MethodOf(const ClassDecl* cls, std::string_view name,
                           const CompilationUnit* unit) {
  const ClassMember* method =
      ClassMemberOf(cls, name, ClassMemberKind::kMethod, unit);
  return method == nullptr ? nullptr : method->method;
}

}  // namespace delta
