#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

void ResolveFormalAggregateTypes(ModuleItem* item, const TypedefMap& typedefs,
                                 Arena& arena) {
  for (FunctionArg& arg : item->func_args) {
    ResolveNestedAggregateTypes(arg.data_type, typedefs, arena);
  }
}

namespace {

void ResolveGenerateBlockFormalTypes(const std::vector<ModuleItem*>& items,
                                     const TypedefMap& typedefs, Arena& arena) {
  bool declares_typedef = false;
  for (const auto* item : items) {
    declares_typedef |= item->kind == ModuleItemKind::kTypedef;
  }
  if (!declares_typedef) {
    ResolveModuleSubroutineFormalTypes(items, typedefs, arena);
    return;
  }
  TypedefMap visible = typedefs;
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kTypedef) visible.erase(item->name);
  }
  ResolveModuleSubroutineFormalTypes(items, visible, arena);
}

}  // namespace

void ResolveModuleSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                        const TypedefMap& typedefs,
                                        Arena& arena) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      ResolveFormalAggregateTypes(item, typedefs, arena);
      continue;
    }
    ResolveGenerateBlockFormalTypes(item->gen_body, typedefs, arena);
    if (item->gen_else != nullptr) {
      ResolveModuleSubroutineFormalTypes({item->gen_else}, typedefs, arena);
    }
    for (const auto& arm : item->gen_case_items) {
      ResolveGenerateBlockFormalTypes(arm.body, typedefs, arena);
    }
  }
}

namespace {

TypedefMap ClassScopeTypedefs(const ClassDecl* cls, const TypedefMap& outer) {
  TypedefMap typedefs = outer;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kTypedef || m->typedef_item == nullptr)
      continue;
    typedefs[m->name] = m->typedef_item->typedef_type;
  }
  return typedefs;
}

void ResolveScopeSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                       const TypedefMap& typedefs,
                                       Arena& arena) {
  ResolveModuleSubroutineFormalTypes(items, typedefs, arena);
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      ResolveClassMethodFormalTypes(item->class_decl, typedefs, arena);
    }
  }
}

TypedefMap PackageQualifiedTypedefs(const CompilationUnit* unit,
                                    const TypedefMap& typedefs) {
  TypedefMap qualified;
  for (const auto& [key, type] : typedefs) {
    auto sep = key.find("::");
    if (sep == std::string_view::npos) continue;
    for (const auto* pkg : unit->packages) {
      if (pkg->name != key.substr(0, sep)) continue;
      qualified.emplace(key, type);
      break;
    }
  }
  return qualified;
}

}  // namespace

void ResolveClassMethodFormalTypes(ClassDecl* cls, const TypedefMap& outer,
                                   Arena& arena) {
  TypedefMap typedefs = ClassScopeTypedefs(cls, outer);
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      ResolveFormalAggregateTypes(m->method, typedefs, arena);
    } else if (m->kind == ClassMemberKind::kClassDecl &&
               m->nested_class != nullptr) {
      ResolveClassMethodFormalTypes(m->nested_class, typedefs, arena);
    }
  }
}

void ResolveModuleClassFormalTypes(const std::vector<ClassDecl*>& classes,
                                   const TypedefMap& typedefs, Arena& arena) {
  for (auto* cls : classes) {
    if (cls != nullptr) ResolveClassMethodFormalTypes(cls, typedefs, arena);
  }
}

void ResolveUnitScopeFormalTypes(CompilationUnit* unit,
                                 const TypedefMap& typedefs, Arena& arena) {
  const TypedefMap kQualified = PackageQualifiedTypedefs(unit, typedefs);
  for (auto* pkg : unit->packages) {
    ResolveScopeSubroutineFormalTypes(
        pkg->items, DpiScopeTypedefs(pkg->items, unit, kQualified), arena);
  }
  TypedefMap unit_typedefs = DpiScopeTypedefs(unit->cu_items, unit, typedefs);
  ResolveScopeSubroutineFormalTypes(unit->cu_items, unit_typedefs, arena);
  for (auto* cls : unit->classes) {
    ResolveClassMethodFormalTypes(cls, unit_typedefs, arena);
  }
}

}  // namespace delta
