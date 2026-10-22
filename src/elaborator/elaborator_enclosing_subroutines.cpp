#include "elaborator/elaborator_enclosing_subroutines.h"

#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

bool IsSubroutineItem(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kTaskDecl ||
         item.kind == ModuleItemKind::kFunctionDecl ||
         item.kind == ModuleItemKind::kDpiImport ||
         item.kind == ModuleItemKind::kDpiExport;
}

bool InterfaceDeclaresSubroutine(const CompilationUnit& unit,
                                 std::string_view iface,
                                 std::string_view name) {
  bool declares = false;
  for (const ModuleDecl* decl : unit.interfaces) {
    if (decl->name != iface) continue;
    for (const ModuleItem* item : decl->items) {
      if (IsSubroutineItem(*item) && item->name == name) declares = true;
    }
  }
  return declares;
}

std::unordered_set<std::string_view> EnclosingSubroutineNames(
    const CompilationUnit& unit, std::string_view module) {
  std::unordered_set<std::string_view> names;
  std::unordered_set<std::string_view> reached{module};
  std::vector<std::string_view> work{module};
  while (!work.empty()) {
    const std::string_view kChild = work.back();
    work.pop_back();
    for (const ModuleDecl* parent : unit.modules) {
      std::unordered_set<std::string_view> children;
      CollectInstantiatedNames(parent->items, children);
      if (!children.contains(kChild) || !reached.insert(parent->name).second) {
        continue;
      }
      for (const ModuleItem* item : parent->items) {
        if (IsSubroutineItem(*item)) names.insert(item->name);
      }
      work.push_back(parent->name);
    }
  }
  return names;
}

// Whether `items`, or the items of a declaration nested among them at any
// depth, declare `nested`; where they do, the imports written above each
// declaration on the way to it are appended to `out`, innermost scope's first.
static bool CollectImportsAbove(const std::vector<ModuleItem*>& items,
                                const ModuleDecl& nested,
                                std::vector<ModuleItem*>& out) {
  std::vector<ModuleItem*> imports;
  for (ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kImportDecl) imports.push_back(item);
    if (item->kind != ModuleItemKind::kNestedModuleDecl) continue;
    if (item->nested_module_decl == &nested ||
        CollectImportsAbove(item->nested_module_decl->items, nested, out)) {
      out.insert(out.end(), imports.begin(), imports.end());
      return true;
    }
  }
  return false;
}

std::vector<ModuleItem*> EnclosingImportsAbove(const CompilationUnit& unit,
                                               const ModuleDecl& decl) {
  std::vector<ModuleItem*> imports;
  for (const std::vector<ModuleDecl*>* decls :
       {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* outer : *decls) {
      if (CollectImportsAbove(outer->items, decl, imports)) return imports;
    }
  }
  return imports;
}

}  // namespace delta
