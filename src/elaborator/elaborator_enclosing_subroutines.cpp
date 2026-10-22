#include "elaborator/elaborator_enclosing_subroutines.h"

#include <algorithm>
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
// depth, declare `nested`; where they do, the imports of each scope on the way
// to it are appended to `out`, innermost scope's first: every import written
// above the declaration leading to `nested`, and each explicit one below it.
static bool CollectEnclosingImports(const std::vector<ModuleItem*>& items,
                                    const ModuleDecl& nested,
                                    EnclosingImports& out) {
  const auto kLeading =
      std::find_if(items.begin(), items.end(), [&](const ModuleItem* item) {
        return item->kind == ModuleItemKind::kNestedModuleDecl &&
               (item->nested_module_decl == &nested ||
                CollectEnclosingImports(item->nested_module_decl->items, nested,
                                        out));
      });
  if (kLeading == items.end()) return false;
  for (auto it = items.begin(); it != items.end(); ++it) {
    if ((*it)->kind != ModuleItemKind::kImportDecl) continue;
    if (it < kLeading) {
      out.above.push_back(*it);
    } else if (!(*it)->import_item.is_wildcard) {
      out.explicit_below.push_back(*it);
    }
  }
  return true;
}

EnclosingImports EnclosingImportsOf(const CompilationUnit& unit,
                                    const ModuleDecl& decl) {
  EnclosingImports imports;
  for (const std::vector<ModuleDecl*>* decls :
       {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* outer : *decls) {
      if (CollectEnclosingImports(outer->items, decl, imports)) return imports;
    }
  }
  return imports;
}

}  // namespace delta
