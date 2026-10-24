#include "elaborator/attached_call_target.h"

#include <algorithm>
#include <string_view>
#include <vector>

#include "elaborator/assertion_walk.h"
#include "elaborator/elaborator_helpers.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

bool IsSubroutineKind(ModuleItemKind kind) {
  return kind == ModuleItemKind::kTaskDecl ||
         kind == ModuleItemKind::kFunctionDecl ||
         kind == ModuleItemKind::kDpiImport;
}

// The task, function or DPI-imported subroutine named `name` among `items`.
const ModuleItem* SubroutineAmong(const std::vector<ModuleItem*>& items,
                                  std::string_view name) {
  const auto kFound =
      std::ranges::find_if(items, [name](const ModuleItem* item) {
        return item->name == name && IsSubroutineKind(item->kind);
      });
  return kFound == items.end() ? nullptr : *kFound;
}

// The items of the package the unit declares as `name`; none where it
// declares no such package.
const std::vector<ModuleItem*>& PackageItems(const CompilationUnit& unit,
                                             std::string_view name) {
  static const std::vector<ModuleItem*> kNone;
  for (const PackageDecl* package : unit.packages) {
    if (package->name == name) return package->items;
  }
  return kNone;
}

// §26.3: the subroutine `name` that an import among `items` makes visible,
// `import p::name;` or `import p::*;` of a package declaring it.
const ModuleItem* ImportedSubroutine(const std::vector<ModuleItem*>& items,
                                     std::string_view name,
                                     const CompilationUnit& unit) {
  for (const ModuleItem* item : items) {
    const ImportItem& spec = item->import_item;
    if (item->kind != ModuleItemKind::kImportDecl ||
        (!spec.is_wildcard && spec.item_name != name)) {
      continue;
    }
    const ModuleItem* found =
        SubroutineAmong(PackageItems(unit, spec.package_name), name);
    if (found != nullptr) return found;
  }
  return nullptr;
}

// §8.13: the method `name` of `cls` or of a class it extends.
const ModuleItem* MethodOf(const ClassDecl* cls, std::string_view name,
                           const CompilationUnit& unit) {
  for (; cls != nullptr; cls = FindBaseClass(cls, &unit)) {
    for (const ClassMember* member : cls->members) {
      if (member->kind == ClassMemberKind::kMethod && member->name == name) {
        return member->method;
      }
    }
  }
  return nullptr;
}

// The class whose handle the variable `name` among `items` is declared to
// hold; null where `name` is no variable there or its type names no class.
const ClassDecl* HandleClassOf(const std::vector<ModuleItem*>& items,
                               std::string_view name,
                               const CompilationUnit& unit) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == name) {
      return FindClassDecl(item->data_type.type_name, &unit);
    }
  }
  return nullptr;
}

// §23.9 and §26.3: the subroutine a name alone calls from `decl`.
const ModuleItem* NamedSubroutine(std::string_view name, const ModuleDecl& decl,
                                  const CompilationUnit& unit) {
  if (const ModuleItem* own = SubroutineAmong(decl.items, name)) return own;
  if (const ModuleItem* imported = ImportedSubroutine(decl.items, name, unit)) {
    return imported;
  }
  return SubroutineAmong(unit.cu_items, name);
}

}  // namespace

const ModuleItem* AttachedCallTarget(const Expr& call,
                                     const ModuleInUnit& scope) {
  const ModuleDecl& decl = scope.decl;
  const CompilationUnit& unit = scope.unit;
  if (IsNameRef(call.lhs, call.callee)) {
    return NamedSubroutine(call.callee, decl, unit);
  }
  const Expr& access = *call.lhs;
  const std::string_view kScope = access.lhs->text;
  const std::string_view kName = access.rhs->text;
  if (!access.is_scope_resolution) {
    return MethodOf(HandleClassOf(decl.items, kScope, unit), kName, unit);
  }
  if (const ModuleItem* found =
          SubroutineAmong(PackageItems(unit, kScope), kName)) {
    return found;
  }
  return MethodOf(FindClassDecl(kScope, &unit), kName, unit);
}

}  // namespace delta
