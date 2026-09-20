// §26.3 with §8.4 and §8.7: a package variable declared with a class's name,
// `C global_h;` in package p, is a handle of that class, and the `new` written
// to it through the package scope resolution operator, `p::global_h = new`,
// constructs an object of that class exactly as `h = new` does for a module's
// `C h;`. The `new` carries no class of its own -- TryClassNewAssign in
// src/simulator/statement_assign_object.cpp asks
// SimContext::GetVariableClassType for the target's -- and Lowerer::LowerVar
// records a module variable's class as it creates it, while a package
// variable's storage is created under its "p.global_h" key
// (InitPackageDataVariables in lowerer_register.cpp) with no class recorded
// under that key, so the handle stayed null. Each package variable whose type
// names a class is recorded here under the same key, for the whole design,
// ahead of every module.

#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"

namespace delta {

// Whether package `pkg` declares a class named `name` among its own items.
static bool PackageDeclaresClass(const PackageDecl* pkg,
                                 std::string_view name) {
  for (const auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
        item->class_decl->name == name)
      return true;
  }
  return false;
}

static const PackageDecl* FindDesignPackage(const RtlirDesign* design,
                                            std::string_view name) {
  for (const auto* pkg : design->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

// The package whose class the type name `name`, written in package `pkg`
// without a scope, denotes: `pkg` itself when it declares one so named, else
// the first package an import of `pkg` brings the name in from -- a wildcard
// import, or an explicit import of that very name (§26.3). Null where no
// package in reach declares a class of the name, which is a typedef'd
// structure, an enumeration or a type nothing declares, none of which a `new`
// constructs. §26.2 keeps a package from naming the compilation unit's
// declarations, so the unit's classes are not searched.
static const PackageDecl* PackageDeclaringClass(const RtlirDesign* design,
                                                const PackageDecl* pkg,
                                                std::string_view name) {
  if (PackageDeclaresClass(pkg, name)) return pkg;
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (!imp.is_wildcard && imp.item_name != name) continue;
    const PackageDecl* source = FindDesignPackage(design, imp.package_name);
    if (source != nullptr && PackageDeclaresClass(source, name)) return source;
  }
  return nullptr;
}

// The key SimContext holds the class that `type`, the declared type of a
// variable of package `pkg`, names under: "q::C", the key LowerPackageClass in
// src/simulator/lowerer_import.cpp registers every package's class by, whether
// the declaration wrote the package itself (`q::C h`) or left it to be found
// through the declaring package and its imports. Empty where the type names
// no class.
static std::string PackageClassKey(const RtlirDesign* design,
                                   const PackageDecl* pkg,
                                   const DataType& type) {
  if (type.kind != DataTypeKind::kNamed || type.type_name.empty()) return {};
  const PackageDecl* owner =
      type.scope_name.empty()
          ? PackageDeclaringClass(design, pkg, type.type_name)
          : FindDesignPackage(design, type.scope_name);
  if (owner == nullptr || !PackageDeclaresClass(owner, type.type_name))
    return {};
  return std::string(owner->name) + "::" + std::string(type.type_name);
}

void RegisterPackageClassVariables(const RtlirDesign* design, SimContext& ctx,
                                   Arena& arena) {
  for (const auto* pkg : design->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kVarDecl) continue;
      std::string key = PackageClassKey(design, pkg, item->data_type);
      if (key.empty()) continue;
      // SimContext keys the record by string_view, so both names are given
      // the design's lifetime.
      auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                              std::string(item->name));
      ctx.SetVariableClassType(*qname, *arena.Create<std::string>(key));
    }
  }
}

}  // namespace delta
