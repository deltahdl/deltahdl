#include <algorithm>
#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/package_references.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/unit_scope_items.h"

namespace delta {

PackageDecl* Lowerer::FindPackage(std::string_view name) const {
  if (!design_) return nullptr;
  for (auto* pkg : design_->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

static std::string_view QualifiedClassKey(const PackageDecl* pkg,
                                          const ClassDecl* cls, Arena& arena) {
  auto* key = arena.Create<std::string>(std::string(pkg->name) +
                                        "::" + std::string(cls->name));
  return *key;
}

void Lowerer::LowerPackageClass(const PackageDecl* pkg, const ClassDecl* cls) {
  std::string_view key = QualifiedClassKey(pkg, cls, arena_);
  if (ctx_.FindClassType(key)) return;
  LowerClassDecl(cls, pkg->items);
  ctx_.RegisterClassType(key, ctx_.FindClassType(cls->name));
  AliasExportedClassKeys(pkg, cls);
}

static bool IsPackageSubroutine(const ModuleItem* item) {
  return (item->kind == ModuleItemKind::kFunctionDecl ||
          item->kind == ModuleItemKind::kTaskDecl) &&
         item->method_class.empty();
}

static void ImportNamedDeclaration(ModuleItem* item, SimContext& ctx) {
  switch (item->kind) {
    case ModuleItemKind::kLetDecl:
    case ModuleItemKind::kCovergroupDecl:
      if (!ctx.FindLetDecl(item->name)) ctx.RegisterLetDecl(item->name, item);
      return;
    case ModuleItemKind::kSequenceDecl:
      if (!ctx.FindSequenceDecl(item->name)) {
        ctx.RegisterSequenceDecl(item->name, item);
      }
      return;
    case ModuleItemKind::kPropertyDecl:
      if (!ctx.FindPropertyDecl(item->name)) {
        ctx.RegisterPropertyDecl(item->name, item);
      }
      return;
    default:
      return;
  }
}

void Lowerer::LowerPackageItem(const PackageDecl* pkg, ModuleItem* item) {
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    if (ctx_.FindClassType(item->class_decl->name)) return;
    ClassTypeInfo* lowered =
        ctx_.FindClassType(QualifiedClassKey(pkg, item->class_decl, arena_));
    if (lowered) {
      ctx_.RegisterClassType(item->class_decl->name, lowered);
    } else {
      LowerPackageClass(pkg, item->class_decl);
    }
  } else if (IsPackageSubroutine(item)) {
    if (!ctx_.FindFunction(item->name)) {
      ctx_.RegisterFunction(item->name, item);
    }
  } else {
    ImportNamedDeclaration(item, ctx_);
  }
}

static bool PackageItemHasName(const ModuleItem* item, std::string_view name) {
  if (item->name == name) return true;
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
      item->class_decl->name == name)
    return true;
  return false;
}

static bool IsImportOrExportDecl(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kImportDecl ||
         item->kind == ModuleItemKind::kExportDecl;
}

static ModuleItem* FindNamedPackageItem(const PackageDecl* pkg,
                                        std::string_view name) {
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    if (PackageItemHasName(item, name)) return item;
  }
  return nullptr;
}

static std::vector<std::string_view> WildcardExportImportNames(
    const PackageDecl* pkg) {
  std::vector<std::string_view> names;
  for (auto* imp_item : pkg->items) {
    if (imp_item->kind != ModuleItemKind::kImportDecl) continue;
    names.push_back(imp_item->import_item.package_name);
  }
  return names;
}

void Lowerer::LowerImportedName(
    PackageDecl* pkg, std::string_view name,
    std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  if (auto* found = FindNamedPackageItem(pkg, name)) {
    LowerPackageItem(pkg, found);
    AliasPackageDataItem(pkg, found);
    return;
  }
  if (AliasPackageEnumMember(pkg, name)) return;

  auto recurse = [&](std::string_view pkg_name) {
    auto* src = FindPackage(pkg_name);
    if (!src) return;
    auto sub = visited;
    LowerImportedName(src, name, sub);
  };
  auto handle_export = [&](const ImportItem& ex) {
    if (ex.package_name == "*") {
      for (std::string_view src_name : WildcardExportImportNames(pkg))
        recurse(src_name);
    } else if (ex.is_wildcard || ex.item_name == name) {
      recurse(ex.package_name);
    }
  };

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    handle_export(item->import_item);
  }
}

namespace {
struct ReExportWalk {
  PackageDecl* pkg;
  const std::unordered_set<std::string_view>& referenced;
  const std::unordered_set<const PackageDecl*>& visited;
  std::function<PackageDecl*(std::string_view)> find_pkg;
  std::function<void(PackageDecl*, std::string_view)> lower_named;
};

void ReExportReferencedCandidates(const ReExportWalk& w, PackageDecl* src) {
  for (const auto* item : src->items) {
    if (IsImportOrExportDecl(item)) continue;
    for (std::string_view name : w.referenced) {
      if (PackageItemHasName(item, name)) w.lower_named(src, name);
    }
  }
  std::vector<std::string_view> rest;
  for (std::string_view name : w.referenced) {
    if (FindNamedPackageItem(src, name) == nullptr) rest.push_back(name);
  }
  std::ranges::sort(rest);
  for (std::string_view name : rest) w.lower_named(src, name);
}

void ReExportImport(const ReExportWalk& w, PackageDecl* src,
                    const ImportItem& imp) {
  if (imp.is_wildcard) {
    ReExportReferencedCandidates(w, src);
  } else {
    w.lower_named(src, imp.item_name);
  }
}

void ReExportWildcardStar(const ReExportWalk& w) {
  for (const auto* item : w.pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (auto* src = w.find_pkg(item->import_item.package_name))
      ReExportImport(w, src, item->import_item);
  }
}

void ReExportFromPackage(const ReExportWalk& w, PackageDecl* src,
                         const ImportItem& ex) {
  if (!ex.is_wildcard) {
    w.lower_named(src, ex.item_name);
    return;
  }
  for (const auto* item : w.pkg->items) {
    if (item->kind == ModuleItemKind::kImportDecl &&
        item->import_item.package_name == src->name) {
      ReExportImport(w, src, item->import_item);
    }
  }
}

void HandleReExport(const ReExportWalk& w, const ImportItem& ex) {
  if (ex.package_name == "*") {
    ReExportWildcardStar(w);
  } else if (auto* src = w.find_pkg(ex.package_name)) {
    ReExportFromPackage(w, src, ex);
  }
}
}  // namespace

void Lowerer::LowerAllImported(
    PackageDecl* pkg, std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    LowerPackageItem(pkg, item);
    AliasPackageDataItem(pkg, item);
  }

  const std::unordered_set<std::string_view> kReferenced =
      PackageReferencedNames(pkg);
  ReExportWalk walk{pkg, kReferenced, visited,
                    [this](std::string_view name) { return FindPackage(name); },
                    [this, &visited](PackageDecl* src, std::string_view name) {
                      auto sub = visited;
                      LowerImportedName(src, name, sub);
                    }};
  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    HandleReExport(walk, item->import_item);
  }
}

static std::string PackageQualifiedName(const PackageDecl* pkg,
                                        std::string_view name) {
  return std::string(pkg->name) + "." + std::string(name);
}

void Lowerer::AliasPackageDataItem(const PackageDecl* pkg,
                                   const ModuleItem* item) {
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  if (!(is_var || (is_param && item->init_expr))) return;
  AliasImportedPackageName(item->name, PackageQualifiedName(pkg, item->name));
}

bool Lowerer::AliasPackageEnumMember(const PackageDecl* pkg,
                                     std::string_view name) {
  std::string qname = PackageQualifiedName(pkg, name);
  if (ctx_.GetVariables().count(qname) == 0) return false;
  AliasImportedPackageName(name, qname);
  return true;
}

bool ModuleDeclaresName(const RtlirModule* mod, std::string_view name) {
  if (mod == nullptr) return false;
  for (const auto& var : mod->variables) {
    if (var.name == name) return true;
  }
  for (const auto& port : mod->ports) {
    if (port.name == name) return true;
  }
  for (const auto& net : mod->nets) {
    if (net.name == name) return true;
  }
  return false;
}

void Lowerer::AliasImportedPackageName(std::string_view name,
                                       std::string_view qname) {
  bool block_import = !import_scope_prefix_.empty();
  if (!block_import && ModuleDeclaresName(importing_module_, name)) return;
  std::string key =
      inst_prefix_ + std::string(import_scope_prefix_) + std::string(name);
  if (ctx_.GetVariables().count(key) != 0) return;
  auto* stored = arena_.Create<std::string>(key);
  ctx_.AliasVariable(*stored, qname);
  AliasVariableKinds(*stored, qname, ctx_, arena_);
  if (!block_import) ctx_.RegisterImportedName(*stored);
}

void Lowerer::AliasAllPackageDataItems(const PackageDecl* pkg) {
  for (const auto* item : pkg->items) AliasPackageDataItem(pkg, item);
}

void Lowerer::AliasNamedPackageDataItem(const PackageDecl* pkg,
                                        std::string_view item_name) {
  for (const auto* item : pkg->items) {
    if (item->name == item_name) AliasPackageDataItem(pkg, item);
  }
}

void Lowerer::LowerOneImport(const ImportItem& imp) {
  auto* pkg = FindPackage(imp.package_name);
  if (!pkg) return;
  std::unordered_set<const PackageDecl*> visited;
  if (imp.is_wildcard) {
    LowerAllImported(pkg, visited);
    AliasAllPackageDataItems(pkg);
  } else {
    LowerImportedName(pkg, imp.item_name, visited);
    AliasNamedPackageDataItem(pkg, imp.item_name);
  }
}

static std::string_view SubroutineImportScopeKey(const RtlirModule* mod,
                                                 const ModuleItem* func,
                                                 Arena& arena) {
  auto* key = arena.Create<std::string>("$import:" + std::string(mod->name) +
                                        "::" + std::string(func->name));
  return *key;
}

static std::vector<const ImportItem*> BodyImportItems(const ModuleItem* func) {
  std::vector<const ImportItem*> imports;
  for (const Stmt* stmt : func->func_body_stmts) {
    if (stmt == nullptr || stmt->kind != StmtKind::kBlockItemDecl) continue;
    const ModuleItem* decl = stmt->decl_item;
    if (decl != nullptr && decl->kind == ModuleItemKind::kImportDecl) {
      imports.push_back(&decl->import_item);
    }
  }
  return imports;
}

static void LowerSubroutineBodyImports(const RtlirModule* mod, SimContext& ctx,
                                       Arena& arena) {
  for (const ModuleItem* func : mod->function_decls) {
    if (!func->method_class.empty()) continue;
    if (!ctx.SubroutinePackage(func).empty()) continue;
    std::vector<const ImportItem*> imports = BodyImportItems(func);
    if (imports.empty()) continue;
    std::string_view key = SubroutineImportScopeKey(mod, func, arena);
    for (const ImportItem* imp : imports) {
      ctx.RegisterPackageImport(key, imp->package_name,
                                imp->is_wildcard ? "*" : imp->item_name);
    }
    ctx.RegisterSubroutinePackage(func, key);
  }
}

void Lowerer::LowerImports(const RtlirModule* mod) {
  LowerSubroutineBodyImports(mod, ctx_, arena_);
  importing_module_ = mod;
  auto apply_import = [&](const RtlirImport& imp) {
    ImportItem item;
    item.package_name = imp.package_name;
    item.item_name = imp.item_name;
    item.is_wildcard = imp.is_wildcard;
    import_scope_prefix_ = imp.scope_prefix;
    LowerOneImport(item);
    import_scope_prefix_ = {};
  };

  for (const auto& imp : mod->imports)
    if (!imp.is_wildcard) apply_import(imp);
  for (const auto& imp : mod->imports)
    if (imp.is_wildcard) apply_import(imp);
  if (mod->unit_index >= 0) {
    LowerUnitImportItems(
        design_->compilation_units[static_cast<size_t>(mod->unit_index)]
            ->cu_items);
  }
  importing_module_ = nullptr;
  AliasUnitDataItems(design_, mod, inst_prefix_, ctx_, arena_);
}

namespace {
struct ExportedName {
  std::string_view name;
  const PackageDecl* origin = nullptr;
  ModuleItem* item = nullptr;
};

using PackageSet = std::unordered_set<const PackageDecl*>;

void CollectEnumConstantNames(const DataType& type, ScopeMap& values,
                              Arena& arena,
                              std::vector<std::string_view>& names) {
  for (const RtlirEnumMember& m :
       FoldEnumMembers(type.enum_members, values, arena)) {
    values[m.name] = m.value;
    names.push_back(m.name);
  }
  for (const StructMember& sm : type.struct_members) {
    if (sm.nested_type != nullptr)
      CollectEnumConstantNames(*sm.nested_type, values, arena, names);
  }
}

std::vector<std::string_view> PackageEnumConstantNames(const PackageDecl* pkg,
                                                       const SimContext& ctx,
                                                       Arena& arena) {
  std::vector<std::string_view> names;
  ScopeMap values;
  for (const ModuleItem* item : pkg->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      if (auto v = FoldPackageParamValue(*item, *pkg, values, ctx))
        values[item->name] = *v;
      continue;
    }
    CollectEnumConstantNames(item->typedef_type, values, arena, names);
    CollectEnumConstantNames(item->data_type, values, arena, names);
  }
  return names;
}

class ExportedNameWalk {
 public:
  ExportedNameWalk(const RtlirDesign* design, const SimContext& ctx,
                   Arena& arena)
      : design_(design), ctx_(ctx), arena_(arena) {}

  void CollectExported(const PackageDecl* pkg, PackageSet visited,
                       std::vector<ExportedName>& out);

 private:
  const PackageDecl* Find(std::string_view name) const;
  const std::vector<std::string_view>& EnumConstantNames(
      const PackageDecl* pkg);
  bool DeclaresEnumConstant(const PackageDecl* pkg, std::string_view name);
  void CollectProvided(const PackageDecl* pkg, PackageSet visited,
                       std::vector<ExportedName>& out);
  void CollectFromExports(const PackageDecl* pkg, const PackageSet& visited,
                          std::vector<ExportedName>& out);
  void CollectReferencedProvided(const PackageDecl* pkg, const PackageDecl* src,
                                 const PackageSet& visited,
                                 std::vector<ExportedName>& out);
  void CollectImportsFrom(const PackageDecl* pkg, std::string_view src_name,
                          const PackageSet& visited,
                          std::vector<ExportedName>& out);
  void CollectNamed(const PackageDecl* src, std::string_view name,
                    const PackageSet& visited, std::vector<ExportedName>& out);

  const RtlirDesign* design_;
  const SimContext& ctx_;
  Arena& arena_;
  std::unordered_map<const PackageDecl*, std::vector<std::string_view>>
      enum_names_;
};

const PackageDecl* ExportedNameWalk::Find(std::string_view name) const {
  for (const PackageDecl* pkg : design_->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

const std::vector<std::string_view>& ExportedNameWalk::EnumConstantNames(
    const PackageDecl* pkg) {
  auto it = enum_names_.find(pkg);
  if (it == enum_names_.end()) {
    it = enum_names_.emplace(pkg, PackageEnumConstantNames(pkg, ctx_, arena_))
             .first;
  }
  return it->second;
}

bool ExportedNameWalk::DeclaresEnumConstant(const PackageDecl* pkg,
                                            std::string_view name) {
  for (std::string_view m : EnumConstantNames(pkg)) {
    if (m == name) return true;
  }
  return false;
}

void ExportedNameWalk::CollectExported(const PackageDecl* pkg,
                                       PackageSet visited,
                                       std::vector<ExportedName>& out) {
  if (!visited.insert(pkg).second) return;
  CollectFromExports(pkg, visited, out);
}

void ExportedNameWalk::CollectProvided(const PackageDecl* pkg,
                                       PackageSet visited,
                                       std::vector<ExportedName>& out) {
  if (!visited.insert(pkg).second) return;
  for (ModuleItem* item : pkg->items) {
    if (IsImportOrExportDecl(item) || item->name.empty()) continue;
    out.push_back({item->name, pkg, item});
  }
  for (std::string_view m : EnumConstantNames(pkg)) {
    out.push_back({m, pkg, nullptr});
  }
  CollectFromExports(pkg, visited, out);
}

void ExportedNameWalk::CollectFromExports(const PackageDecl* pkg,
                                          const PackageSet& visited,
                                          std::vector<ExportedName>& out) {
  for (const ModuleItem* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const ImportItem& ex = item->import_item;
    if (ex.package_name == "*" || ex.is_wildcard) {
      CollectImportsFrom(pkg, ex.package_name, visited, out);
    } else if (const PackageDecl* src = Find(ex.package_name)) {
      CollectNamed(src, ex.item_name, visited, out);
    }
  }
}

void ExportedNameWalk::CollectReferencedProvided(
    const PackageDecl* pkg, const PackageDecl* src, const PackageSet& visited,
    std::vector<ExportedName>& out) {
  std::vector<ExportedName> provided;
  CollectProvided(src, visited, provided);
  const std::unordered_set<std::string_view> kReferenced =
      PackageReferencedNames(pkg);
  for (const ExportedName& e : provided) {
    if (kReferenced.contains(e.name)) out.push_back(e);
  }
}

void ExportedNameWalk::CollectImportsFrom(const PackageDecl* pkg,
                                          std::string_view src_name,
                                          const PackageSet& visited,
                                          std::vector<ExportedName>& out) {
  for (const ModuleItem* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (src_name != "*" && imp.package_name != src_name) continue;
    const PackageDecl* src = Find(imp.package_name);
    if (src == nullptr) continue;
    if (imp.is_wildcard) {
      CollectReferencedProvided(pkg, src, visited, out);
    } else {
      CollectNamed(src, imp.item_name, visited, out);
    }
  }
}

void ExportedNameWalk::CollectNamed(const PackageDecl* src,
                                    std::string_view name,
                                    const PackageSet& visited,
                                    std::vector<ExportedName>& out) {
  if (ModuleItem* item = FindNamedPackageItem(src, name)) {
    out.push_back({name, src, item});
    return;
  }
  if (DeclaresEnumConstant(src, name)) {
    out.push_back({name, src, nullptr});
    return;
  }
  std::vector<ExportedName> handed_on;
  CollectExported(src, visited, handed_on);
  for (const ExportedName& e : handed_on) {
    if (e.name == name) out.push_back(e);
  }
}

void AliasExportedName(const PackageDecl* pkg, const ExportedName& e,
                       SimContext& ctx, Arena& arena) {
  if (e.origin == pkg || e.name.empty()) return;
  bool subroutine =
      e.item != nullptr && (e.item->kind == ModuleItemKind::kFunctionDecl ||
                            e.item->kind == ModuleItemKind::kTaskDecl);
  if (subroutine) {
    if (!e.item->method_class.empty()) return;
    std::string key = std::string(pkg->name) + "::" + std::string(e.name);
    if (ctx.FindFunction(key) != nullptr) return;
    ctx.RegisterFunction(*arena.Create<std::string>(key), e.item);
    return;
  }
  std::string qname = PackageQualifiedName(e.origin, e.name);
  if (ctx.GetVariables().count(qname) == 0) return;
  std::string key = PackageQualifiedName(pkg, e.name);
  if (ctx.GetVariables().count(key) != 0) return;
  std::string_view stored = *arena.Create<std::string>(key);
  ctx.AliasVariable(stored, qname);
  AliasVariableKinds(stored, qname, ctx, arena);
}

}  // namespace

void AliasPackageExports(const RtlirDesign* design, SimContext& ctx,
                         Arena& arena) {
  ExportedNameWalk walk(design, ctx, arena);
  for (const PackageDecl* pkg : design->packages) {
    std::vector<ExportedName> names;
    walk.CollectExported(pkg, {}, names);
    for (const ExportedName& e : names) AliasExportedName(pkg, e, ctx, arena);
  }
}

static bool ExportsHandOnName(ExportedNameWalk& walk,
                              const PackageDecl* exporter,
                              const PackageDecl* pkg, std::string_view name) {
  std::vector<ExportedName> names;
  walk.CollectExported(exporter, {}, names);
  for (const ExportedName& e : names) {
    if (e.origin == pkg && e.name == name) return true;
  }
  return false;
}

void Lowerer::AliasExportedClassKeys(const PackageDecl* pkg,
                                     const ClassDecl* cls) {
  if (design_ == nullptr) return;
  ClassTypeInfo* info = ctx_.FindClassType(QualifiedClassKey(pkg, cls, arena_));
  if (info == nullptr) return;
  ExportedNameWalk walk(design_, ctx_, arena_);
  for (const PackageDecl* exporter : design_->packages) {
    bool own =
        exporter == pkg || FindNamedPackageItem(exporter, cls->name) != nullptr;
    if (own || !ExportsHandOnName(walk, exporter, pkg, cls->name)) continue;
    std::string_view key = QualifiedClassKey(exporter, cls, arena_);
    if (ctx_.FindClassType(key) == nullptr) ctx_.RegisterClassType(key, info);
  }
}

void Lowerer::LowerCompilationUnitImports() {
  if (!design_ || !design_->compilation_unit) return;
  if (!design_->compilation_units.empty()) {
    ForEachUnitScope(design_, arena_,
                     [&](const CompilationUnit& unit, std::string_view scope) {
                       for (const auto* item : unit.cu_items) {
                         if (item->kind != ModuleItemKind::kImportDecl)
                           continue;
                         const ImportItem& imp = item->import_item;
                         ctx_.RegisterPackageImport(
                             scope, imp.package_name,
                             imp.is_wildcard ? "*" : imp.item_name);
                       }
                     });
    return;
  }
  LowerUnitImportItems(design_->compilation_unit->cu_items);
}

void Lowerer::LowerUnitImportItems(const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard) LowerOneImport(item->import_item);
  }
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (item->import_item.is_wildcard) LowerOneImport(item->import_item);
  }
}

void Lowerer::LowerCompilationUnitClasses() {
  const auto kRenamed = ScopeSameNamedUnitClasses(design_, arena_);
  std::unordered_set<std::string_view> unit_class_names;
  for (const auto* cls : UnitClassesToLower(design_)) {
    unit_class_names.insert(cls->name);
    LowerClassDecl(cls, design_->cu_function_decls);
  }
  for (const auto& [bare, scoped] : kRenamed) {
    if (ctx_.FindClassType(bare) == nullptr) {
      ctx_.RegisterClassType(bare, ctx_.FindClassType(scoped));
    }
  }
  if (design_->compilation_unit == nullptr) return;
  for (const auto* item : design_->compilation_unit->cu_items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl ||
        !item->from_anonymous_program) {
      continue;
    }
    if (unit_class_names.insert(item->class_decl->name).second)
      LowerClassDecl(item->class_decl, design_->cu_function_decls);
  }
}

void Lowerer::LowerUnimportedClassesOf(const PackageDecl* pkg) {
  std::vector<std::pair<std::string_view, ClassTypeInfo*>> displaced;
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl) continue;
    const ClassDecl* cls = item->class_decl;
    if (ctx_.FindClassType(QualifiedClassKey(pkg, cls, arena_))) continue;
    if (ClassTypeInfo* held = ctx_.FindClassType(cls->name))
      displaced.emplace_back(cls->name, held);
    LowerPackageClass(pkg, cls);
  }
  for (const auto& [name, held] : displaced) ctx_.RegisterClassType(name, held);
}

}  // namespace delta
