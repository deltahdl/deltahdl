#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

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

static std::string BuiltinClassKey(const DataType& type) {
  if (type.kind != DataTypeKind::kNamed) return {};
  if (!type.scope_name.empty() && type.scope_name != "std") return {};
  if (type.type_name != "process" && type.type_name != "weak_reference")
    return {};
  return std::string(type.type_name);
}

void RegisterPackageClassVariables(const RtlirDesign* design, SimContext& ctx,
                                   Arena& arena) {
  for (const auto* pkg : design->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kVarDecl) continue;
      std::string key = BuiltinClassKey(item->data_type);
      if (key.empty()) key = PackageClassKey(design, pkg, item->data_type);
      if (key.empty()) continue;
      auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                              std::string(item->name));
      ctx.SetVariableClassType(*qname, *arena.Create<std::string>(key));
      RecordClassParamActuals(*qname, key, item->data_type.type_params, ctx);
    }
  }
}

}  // namespace delta
