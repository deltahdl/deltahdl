#include "elaborator/class_base_resolution.h"

#include <cstddef>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/std_package.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The names an extends clause may write: those that name a class or whose
// meaning only elaboration settles, and those a typedef gives a type that is
// no class.
struct BaseNames {
  // Every class's name, nested ones included; every type parameter's and
  // parameter's, of a class or of a module, interface or program; and every
  // typedef's to a named type or forward typedef's (§6.18), which may name a
  // class.
  std::unordered_set<std::string_view> resolving;
  // Every typedef's to a type that is no class, `typedef int T`.
  std::unordered_set<std::string_view> non_class_typedefs;

  void AddTypedef(std::string_view name, const DataType& type) {
    const bool kMayBeClass = type.kind == DataTypeKind::kNamed ||
                             type.kind == DataTypeKind::kImplicit;
    (kMayBeClass ? resolving : non_class_typedefs).insert(name);
  }

  void AddItems(const std::vector<ModuleItem*>& items) {
    for (const ModuleItem* item : items) {
      if (item->kind == ModuleItemKind::kParamDecl)
        resolving.insert(item->name);
      if (item->kind == ModuleItemKind::kTypedef) {
        AddTypedef(item->name, item->typedef_type);
      }
    }
  }
};

BaseNames CollectBaseNames(const CompilationUnit& unit) {
  BaseNames names;
  names.AddItems(unit.cu_items);
  for (const auto* group :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *group) {
      names.AddItems(decl->items);
      names.resolving.insert(decl->type_param_names.begin(),
                             decl->type_param_names.end());
    }
  }
  for (const PackageDecl* package : unit.packages) {
    names.AddItems(package->items);
  }
  for (const ClassDecl* cls : AllClassDecls(&unit)) {
    names.resolving.insert(cls->name);
    names.resolving.insert(cls->type_param_names.begin(),
                           cls->type_param_names.end());
    for (const ClassMember* m : cls->members) {
      if (m->is_param) names.resolving.insert(m->name);
      if (m->typedef_item != nullptr) {
        names.AddTypedef(m->name, m->typedef_item->typedef_type);
      }
    }
  }
  return names;
}

}  // namespace

void ReportBasesNamingNoClass(const CompilationUnit& unit, DiagEngine& diag) {
  const BaseNames kNames = CollectBaseNames(unit);
  for (const ClassDecl* cls : AllClassDecls(&unit)) {
    const std::string_view kBase = cls->base_class;
    if (kBase.empty() || kNames.resolving.contains(kBase) ||
        StdPackageMemberNamed(kBase)) {
      continue;
    }
    if (kNames.non_class_typedefs.contains(kBase)) {
      diag.Error(cls->range.start,
                 std::format("class '{}' extends '{}', a typedef of a type "
                             "that is no class",
                             cls->name, kBase),
                 Subclause("8.25"));
    } else {
      diag.Error(cls->range.start,
                 std::format("class '{}' extends '{}', which nothing declares",
                             cls->name, kBase),
                 Subclause("8.13"));
    }
  }
}

void ReportSpecializationBaseNotClass(const DataType& type, SourceLoc loc,
                                      const CompilationUnit& unit,
                                      DiagEngine& diag) {
  const ClassDecl* cls = FindClassDecl(type.type_name, &unit);
  if (cls == nullptr || !cls->type_param_names.contains(cls->base_class)) {
    return;
  }
  std::size_t index = 0;
  while (cls->params[index].first != cls->base_class) ++index;
  const DataType* arg =
      SpecializationArgument(type.type_params, index, cls->base_class);
  const DataType& bound = arg != nullptr ? *arg : cls->param_types.at(index);
  if (bound.kind == DataTypeKind::kNamed ||
      bound.kind == DataTypeKind::kImplicit) {
    return;
  }
  diag.Error(loc,
             std::format("this specialization of '{}' gives its type "
                         "parameter '{}', the class it extends, a type that "
                         "is no class",
                         cls->name, cls->base_class),
             Subclause("8.25"));
}

}  // namespace delta
