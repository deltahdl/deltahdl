#include "elaborator/elaborator_dpi_names.h"

#include <string_view>
#include <unordered_set>
#include <vector>

#include "parser/ast.h"

namespace delta {

// §26.3: an import declaration makes a package's typedef nameable in the
// importing scope by its bare name, so a DPI formal argument written with that
// name is a typedef reference the §35.5.6 check has to follow. The elaborator's
// compilation-unit table holds a package typedef under its "pkg::name" key
// alone, and the bare-name entry is added while the module is elaborated, which
// is after ValidateDpiGlobalNameSpace has run. This adds the bare name for the
// declaration in hand. A wildcard import brings every typedef of the package;
// an explicit one brings the single name it states.
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

// §35.5.6 permits a type "constructed from the supported types with the help of
// the following constructs: struct, union (packed forms only), unpacked array,
// typedef", so a typedef name is permitted exactly where the type behind the
// name is. Deciding that needs the typedefs visible to the declaration, and a
// scope-local one is not in the elaborator's compilation-unit table, so this
// copies the outer table, adds every typedef the scope declares, and adds every
// typedef the scope's import declarations name. One map then answers for a
// scope-local, an imported, a compilation-unit and a scope-qualified name
// alike.
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

// §35.5.4, footnote 27 of Syntax 35-1: "Formals of dpi_function_proto and
// dpi_task_proto cannot use pass by reference mode and class types cannot be
// passed at all." A class name is in neither the built-in type keywords nor the
// typedef table, so a formal declared with one resolves to nothing and the
// permitted-type checks below pass over it along with every other name they
// cannot see -- which is right for a name the elaborator does not know and
// wrong for this one. The class names are collected so the prohibition can be
// told from that silence.
using DpiClassNames = std::unordered_set<std::string_view>;

DpiClassNames CollectDpiClassNames(
    const CompilationUnit* unit,
    const std::vector<const std::vector<ModuleItem*>*>& scopes) {
  DpiClassNames names;
  // §3.12.1: a class declared outside every design element belongs to the
  // compilation-unit scope, and the parser keeps those in their own list rather
  // than among the unit's items -- which is where a source writes the class an
  // import in a module names.
  for (const auto* decl : unit->classes) {
    if (decl != nullptr) names.insert(decl->name);
  }
  for (const auto* items : scopes) {
    for (const auto* item : *items) {
      // Within a scope the declaration's name is on the ClassDecl rather than
      // on the item, which is where RecordClassDecl reads it too.
      if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
          item->class_decl != nullptr) {
        names.insert(item->class_decl->name);
      }
    }
  }
  return names;
}

// Follow a type name to the type it stands for, so that the permitted set
// §35.5.5 gives a function result and the one §35.5.6 gives a formal argument
// are applied to that type rather than to the name. A built-in keyword wins
// over a table entry, and a name that resolves to another name is followed in
// turn, under a depth bound because a typedef table built from erroneous source
// can cycle. Returns the type reached, which is the type passed in when nothing
// resolved -- the prevailing treatment of an unresolved name is to stay silent
// about it.
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

// Whether `type`, followed through the scope's typedefs, names a class.
// Footnote 27 admits no indirection through which a class may be passed, so a
// `typedef C my_c_t;` used as a formal is the same prohibition as C written
// directly. ResolveDpiTypeName leaves an unresolved chain at the last name it
// reached, which is the name to ask about.
bool NamesAClass(const DataType& type, const TypedefMap& typedefs,
                 const DpiClassNames& classes) {
  if (type.kind != DataTypeKind::kNamed) return false;
  DataType resolved = ResolveDpiTypeName(type, typedefs);
  if (resolved.kind != DataTypeKind::kNamed) return false;
  return classes.count(resolved.type_name) != 0;
}

}  // namespace delta
