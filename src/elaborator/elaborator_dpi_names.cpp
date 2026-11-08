#include "elaborator/elaborator_dpi_names.h"

#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

void AddImportedTypedefs(const ImportItem& import_item,
                         const CompilationUnit* unit, TypedefMap& typedefs) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name != import_item.package_name) continue;
    for (const auto* pi : pkg->items) {
      if (pi->kind != ModuleItemKind::kTypedef) continue;
      if (!import_item.is_wildcard && pi->name != import_item.item_name) {
        continue;
      }
      typedefs[pi->name] = pi->typedef_type;
    }
    return;
  }
}

TypedefMap DpiScopeTypedefs(const std::vector<ModuleItem*>& items,
                            const CompilationUnit* unit,
                            const TypedefMap& outer) {
  TypedefMap typedefs = outer;
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kTypedef) {
      typedefs[item->name] = item->typedef_type;
      continue;
    }
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    AddImportedTypedefs(item->import_item, unit, typedefs);
  }
  return typedefs;
}

using DpiClassNames = std::unordered_set<std::string_view>;

DpiClassNames CollectDpiClassNames(
    const CompilationUnit* unit,
    const std::vector<const std::vector<ModuleItem*>*>& scopes) {
  DpiClassNames names;
  for (const auto* decl : unit->classes) {
    if (decl != nullptr) names.insert(decl->name);
  }
  for (const auto* items : scopes) {
    for (const auto* item : *items) {
      if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
          item->class_decl != nullptr) {
        names.insert(item->class_decl->name);
      }
    }
  }
  return names;
}

DataType ResolveDpiTypeName(const DataType& type, const TypedefMap& typedefs) {
  DataType dt = type;
  for (int depth = 0; depth < 16 && dt.kind == DataTypeKind::kNamed; ++depth) {
    DataType builtin = TypeNameToDataType(dt.type_name);
    if (builtin.kind != DataTypeKind::kNamed) {
      dt = builtin;
      break;
    }
    auto it = typedefs.find(dt.type_name);
    if (it == typedefs.end()) break;
    dt = it->second;
  }
  return dt;
}

bool NamesAClass(const DataType& type, const TypedefMap& typedefs,
                 const DpiClassNames& classes) {
  if (type.kind != DataTypeKind::kNamed) return false;
  DataType resolved = ResolveDpiTypeName(type, typedefs);
  if (resolved.kind != DataTypeKind::kNamed) return false;
  return classes.count(resolved.type_name) != 0;
}

}  // namespace delta
