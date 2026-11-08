#include <algorithm>
#include <cstdint>
#include <format>
#include <functional>
#include <initializer_list>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_body_slots.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_modport_imports.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_assertion_text.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct PackageRefContext {
  const CompilationUnit* unit;
  const std::unordered_set<std::string_view>* known_package_names;
  const std::unordered_set<std::string_view>* cu_top_names;
  std::unordered_set<std::string_view> pkg_names;
  std::unordered_set<std::string_view> imported_names;
  std::unordered_set<std::string_view> wildcard_pkgs;
  ProvidedNameCache* provided_names;
  DiagEngine* diag;
  const std::unordered_set<std::string_view>* design_elements = nullptr;
};

std::unordered_set<std::string_view> CollectCuTopNames(
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> cu_top_names;
  for (const auto* item : unit->cu_items) {
    if (!item->name.empty()) cu_top_names.insert(item->name);
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      cu_top_names.insert(item->class_decl->name);
    }
  }
  for (const auto* cls : unit->classes) cu_top_names.insert(cls->name);
  return cu_top_names;
}

void CollectPackageLocalNames(const PackageDecl* pkg, PackageRefContext& ctx) {
  for (const auto* it : pkg->items) {
    if (!it->name.empty()) ctx.pkg_names.insert(it->name);
    if (it->kind == ModuleItemKind::kClassDecl && it->class_decl) {
      ctx.pkg_names.insert(it->class_decl->name);
    }
    if (it->kind == ModuleItemKind::kImportDecl) {
      if (it->import_item.is_wildcard) {
        ctx.wildcard_pkgs.insert(it->import_item.package_name);
      } else {
        ctx.imported_names.insert(it->import_item.item_name);
      }
    }
  }
}

bool IsProvidedByWildcard(const PackageRefContext& ctx, std::string_view name) {
  for (auto pname : ctx.wildcard_pkgs) {
    if (PackageProvidesName(ctx.unit, *ctx.provided_names, pname, name))
      return true;
  }
  return false;
}

bool IsImportedName(const PackageRefContext& ctx, std::string_view name) {
  return ctx.imported_names.count(name) != 0 || IsProvidedByWildcard(ctx, name);
}

void CheckPackageRefCuName(const PackageRefContext& ctx, std::string_view name,
                           SourceLoc loc) {
  if (ctx.cu_top_names->count(name) && !ctx.pkg_names.count(name) &&
      !IsImportedName(ctx, name)) {
    ctx.diag->Error(loc,
                    std::format("package item references '{}' from the "
                                "compilation-unit scope; packages cannot refer "
                                "to compilation-unit-scope items",
                                name),
                    Subclause("26.2"));
  }
}

void CheckPackageRefIdentifier(const PackageRefContext& ctx, const Expr* e) {
  if (!e->scope_prefix.empty()) {
    ctx.diag->Error(
        e->range.start,
        std::format("package item uses scope prefix '{}', which targets "
                    "a scope outside the package",
                    e->scope_prefix),
        Subclause("26.2"));
  } else {
    CheckPackageRefCuName(ctx, e->text, e->range.start);
  }
}

bool IsStdPackageOrMember(std::string_view name) {
  return name == "std" || StdPackageMemberNamed(name).has_value();
}

bool RootIsOutsidePackage(const PackageRefContext& ctx, std::string_view root) {
  if (ctx.design_elements != nullptr) {
    return ctx.design_elements->count(root) != 0;
  }
  bool is_pkg =
      ctx.known_package_names->count(root) > 0 || IsStdPackageOrMember(root);
  bool is_self = ctx.pkg_names.count(root) > 0;
  return !is_pkg && !is_self && !IsImportedName(ctx, root);
}

void CheckPackageRefRoot(const PackageRefContext& ctx, std::string_view root,
                         SourceLoc loc) {
  if (RootIsOutsidePackage(ctx, root)) {
    ctx.diag->Error(loc,
                    std::format("package item contains a hierarchical "
                                "reference '{}' that does not target the "
                                "package itself or an imported package",
                                root),
                    Subclause("26.2"));
  }
}

void CheckPackageRefMemberRoot(const PackageRefContext& ctx, const Expr* e) {
  if (e->lhs && e->lhs->kind == ExprKind::kIdentifier && e->rhs) {
    CheckPackageRefRoot(ctx, e->lhs->text, e->range.start);
  }
}

void WalkPropertyNode(const PackageRefContext& ctx, PropertyExprNode* node);

void WalkPackageRefExpr(const PackageRefContext& ctx, const Expr* e) {
  if (!e) return;
  WalkPropertyNode(ctx, e->property_actual);
  if (e->kind == ExprKind::kIdentifier) {
    CheckPackageRefIdentifier(ctx, e);
  } else if (e->kind == ExprKind::kMemberAccess) {
    CheckPackageRefMemberRoot(ctx, e);
    WalkPackageRefExpr(ctx, e->lhs);
    WalkPackageRefExpr(ctx, e->base);
    WalkPackageRefExpr(ctx, e->index);
    WalkPackageRefExpr(ctx, e->index_end);
    return;
  }
  WalkPackageRefExpr(ctx, e->lhs);
  WalkPackageRefExpr(ctx, e->rhs);
  WalkPackageRefExpr(ctx, e->base);
  WalkPackageRefExpr(ctx, e->index);
  WalkPackageRefExpr(ctx, e->index_end);
  WalkPackageRefExpr(ctx, e->condition);
  WalkPackageRefExpr(ctx, e->true_expr);
  WalkPackageRefExpr(ctx, e->false_expr);
  WalkPackageRefExpr(ctx, e->repeat_count);
  WalkPackageRefExpr(ctx, e->with_expr);
  WalkPackageRefExpr(ctx, e->stream_range);
  for (const auto* a : e->args) WalkPackageRefExpr(ctx, a);
  for (const auto* el : e->elements) WalkPackageRefExpr(ctx, el);
}

void WalkPackageRefStmt(PackageRefContext& ctx, const Stmt* s) {
  if (s == nullptr) return;
  std::vector<std::string_view> added;
  for (auto name : NamesDeclaredUnder(s)) {
    if (ctx.pkg_names.insert(name).second) added.push_back(name);
  }
  ForEachChildExpr(s, [&](const Expr* e) { WalkPackageRefExpr(ctx, e); });
  ForEachChildStmt(s, [&](const Stmt* sub) { WalkPackageRefStmt(ctx, sub); });
  for (auto name : added) ctx.pkg_names.erase(name);
}

void WalkWithNames(PackageRefContext& ctx,
                   const std::unordered_set<std::string_view>& names,
                   const std::function<void()>& walk) {
  std::vector<std::string_view> added;
  for (auto name : names) {
    if (ctx.pkg_names.insert(name).second) added.push_back(name);
  }
  walk();
  for (auto name : added) ctx.pkg_names.erase(name);
}

void WalkMethodBody(PackageRefContext& ctx, const ModuleItem* method) {
  WalkWithNames(ctx, CollectMethodLocalNames(method), [&] {
    for (const auto* s : method->func_body_stmts) WalkPackageRefStmt(ctx, s);
  });
}

void WalkPackageSubroutine(PackageRefContext& ctx, const ModuleItem* item) {
  bool is_subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                       item->kind == ModuleItemKind::kTaskDecl;
  if (!is_subroutine || !item->method_class.empty()) return;
  WalkMethodBody(ctx, item);
}

void WalkPackageItemInit(PackageRefContext& ctx, const ModuleItem* item) {
  if (item->init_expr == nullptr) return;
  std::unordered_set<std::string_view> formals;
  for (const FunctionArg& arg : item->func_args) formals.insert(arg.name);
  WalkWithNames(ctx, formals,
                [&] { WalkPackageRefExpr(ctx, item->init_expr); });
}

void WalkPropertyNode(const PackageRefContext& ctx, PropertyExprNode* node) {
  if (node == nullptr) return;
  ForEachTreeSlot(node, [&](const Expr* e) { WalkPackageRefExpr(ctx, e); });
}

void WalkPackageProperty(PackageRefContext& ctx, const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kPropertyDecl) return;
  WalkWithNames(ctx, AssertionBoundNames(item), [&] {
    for (const EventExpr& ev : item->prop_clock) {
      WalkPackageRefExpr(ctx, ev.signal);
    }
    WalkPackageRefExpr(ctx, item->prop_disable_iff);
    WalkPackageRefExpr(ctx, item->prop_body_expr);
    WalkPropertyNode(ctx, item->prop_body_tree);
  });
}

void WalkPackageSequenceReads(const PackageRefContext& ctx, ModuleItem* item) {
  std::vector<SourceLoc> clock_names;
  ForEachEventSlot(item->seq_clock, [&](const Expr* slot) {
    ForEachSubExpr(slot, [&](const Expr* e) {
      if (e->kind == ExprKind::kIdentifier)
        clock_names.push_back(e->range.start);
    });
  });
  for (const AssertionRead& read : item->assertion_reads) {
    bool in_clock = std::ranges::any_of(clock_names, [&](SourceLoc loc) {
      return std::tie(loc.file_id, loc.line, loc.column) ==
             std::tie(read.loc.file_id, read.loc.line, read.loc.column);
    });
    if (in_clock) continue;
    CheckPackageRefCuName(ctx, read.name, read.loc);
    if (read.heads_member_access) CheckPackageRefRoot(ctx, read.name, read.loc);
  }
}

void WalkPackageSequence(PackageRefContext& ctx, ModuleItem* item) {
  if (item->kind != ModuleItemKind::kSequenceDecl) return;
  auto walk = [&](const Expr* e) { WalkPackageRefExpr(ctx, e); };
  WalkWithNames(ctx, AssertionBoundNames(item), [&] {
    ForEachEventSlot(item->seq_clock, walk);
    if (item->seq_linear.operands.empty()) {
      WalkPackageSequenceReads(ctx, item);
    } else {
      ForEachBodySlot(item->seq_linear, walk);
    }
  });
}

std::unordered_set<std::string_view> ClassMemberNames(const ClassDecl* cls) {
  std::unordered_set<std::string_view> members;
  for (const auto& [name, value] : cls->params) members.insert(name);
  for (const ClassMember* m : cls->members) {
    members.insert(m->kind == ClassMemberKind::kMethod ? m->method->name
                                                       : m->name);
  }
  return members;
}

void WalkClassBodies(PackageRefContext& ctx, const PackageDecl* pkg,
                     const ClassDecl* cls) {
  for (const ClassMember* m : cls->members) {
    if (m->init_expr != nullptr) WalkPackageRefExpr(ctx, m->init_expr);
    if (m->kind == ClassMemberKind::kMethod) WalkMethodBody(ctx, m->method);
  }
  for (const auto* body : pkg->items) {
    if (body->method_class == cls->name) WalkMethodBody(ctx, body);
  }
}

void WalkPackageClass(PackageRefContext& ctx, const PackageDecl* pkg,
                      const ModuleItem* item,
                      const std::unordered_set<std::string_view>& elements) {
  if (item->kind != ModuleItemKind::kClassDecl) return;
  const ClassDecl* cls = item->class_decl;
  ctx.design_elements = &elements;
  WalkWithNames(ctx, ClassMemberNames(cls),
                [&] { WalkClassBodies(ctx, pkg, cls); });
  ctx.design_elements = nullptr;
}

std::unordered_set<std::string_view> DesignElementNames(
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> names;
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* decl : *scopes) names.insert(decl->name);
  }
  return names;
}

}  // namespace

void Elaborator::ValidatePackageReferences() {
  std::unordered_set<std::string_view> known_package_names;
  for (const auto* pkg : unit_->packages) known_package_names.insert(pkg->name);

  std::unordered_set<std::string_view> cu_top_names = CollectCuTopNames(unit_);
  const std::unordered_set<std::string_view> kDesignElements =
      DesignElementNames(unit_);

  for (const auto* pkg : unit_->packages) {
    PackageRefContext ctx;
    ctx.unit = unit_;
    ctx.known_package_names = &known_package_names;
    ctx.cu_top_names = &cu_top_names;
    ctx.provided_names = &pkg_provided_names_;
    ctx.diag = &diag_;
    CollectPackageLocalNames(pkg, ctx);

    for (ModuleItem* item : pkg->items) {
      WalkPackageItemInit(ctx, item);
      WalkPackageSubroutine(ctx, item);
      WalkPackageProperty(ctx, item);
      WalkPackageSequence(ctx, item);
      WalkPackageClass(ctx, pkg, item, kDesignElements);
    }
  }
}

namespace {

using PkgByName = std::unordered_map<std::string_view, const PackageDecl*>;

struct PackageImportSet {
  std::unordered_set<std::string> direct_imports;
  std::unordered_set<std::string_view> wildcard_sources;
};

std::optional<int64_t> GeneratedIndexOf(std::string_view written,
                                        std::string_view name) {
  if (name.size() <= written.size() || !name.starts_with(written)) {
    return std::nullopt;
  }
  std::string_view digits = name.substr(written.size());
  if (digits.size() > 18 || (digits.size() > 1 && digits[0] == '0')) {
    return std::nullopt;
  }
  int64_t index = 0;
  for (char c : digits) {
    if (c < '0' || c > '9') return std::nullopt;
    index = (index * 10) + (c - '0');
  }
  return index;
}

bool RangedMemberGenerates(const EnumMember& em, std::string_view name) {
  auto index = GeneratedIndexOf(em.name, name);
  if (!index) return false;
  auto n = ConstEvalInt(em.range_start);
  if (!n) return true;
  if (em.range_end == nullptr) return *index < *n;
  auto m = ConstEvalInt(em.range_end);
  if (!m) return true;
  return *n <= *m ? *index >= *n && *index <= *m : *index >= *m && *index <= *n;
}

bool TypeDeclaresEnumLiteral(const DataType& type, std::string_view name) {
  for (const auto& em : type.enum_members) {
    if (em.range_start == nullptr ? em.name == name
                                  : RangedMemberGenerates(em, name)) {
      return true;
    }
  }
  for (const auto& sm : type.struct_members) {
    if (sm.nested_type != nullptr &&
        TypeDeclaresEnumLiteral(*sm.nested_type, name))
      return true;
  }
  return false;
}

bool PackageDeclaresName(const PackageDecl* src_pkg, std::string_view name) {
  for (const auto* it : src_pkg->items) {
    if (it->kind == ModuleItemKind::kImportDecl ||
        it->kind == ModuleItemKind::kExportDecl)
      continue;
    if (it->kind == ModuleItemKind::kClassDecl && it->class_decl &&
        it->class_decl->name == name)
      return true;
    if (!it->name.empty() && it->name == name) return true;
    if (TypeDeclaresEnumLiteral(it->typedef_type, name) ||
        TypeDeclaresEnumLiteral(it->data_type, name))
      return true;
  }
  return false;
}

bool PackageProvidesName(const PackageDecl* src_pkg, std::string_view name,
                         const PkgByName& pkg_by_name,
                         std::unordered_set<const PackageDecl*>& visited);

bool PackageActuallyImports(const PackageDecl* pkg, std::string_view src,
                            std::string_view name) {
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const auto& imp = item->import_item;
    if (imp.package_name != src) continue;
    if (imp.is_wildcard) return true;
    if (imp.item_name == name) return true;
  }
  return false;
}

bool WildcardExportProvidesName(
    const PackageDecl* src_pkg, std::string_view name,
    const PkgByName& pkg_by_name,
    const std::unordered_set<const PackageDecl*>& visited) {
  for (const auto* imp : src_pkg->items) {
    if (imp->kind != ModuleItemKind::kImportDecl) continue;
    const auto& ii = imp->import_item;
    if (!ii.is_wildcard && ii.item_name != name) continue;
    auto sit = pkg_by_name.find(ii.package_name);
    if (sit == pkg_by_name.end()) continue;
    auto sub = visited;
    if (PackageProvidesName(sit->second, name, pkg_by_name, sub)) return true;
  }
  return false;
}

bool NamedExportProvidesName(
    const PackageDecl* exporting_pkg, const ImportItem& ex,
    std::string_view name, const PkgByName& pkg_by_name,
    const std::unordered_set<const PackageDecl*>& visited) {
  auto sit = pkg_by_name.find(ex.package_name);
  if (sit == pkg_by_name.end()) return false;
  if (ex.is_wildcard) {
    if (!PackageActuallyImports(exporting_pkg, ex.package_name, name))
      return false;
  } else if (ex.item_name != name) {
    return false;
  }
  auto sub = visited;
  return PackageProvidesName(sit->second, name, pkg_by_name, sub);
}

bool PackageProvidesName(const PackageDecl* src_pkg, std::string_view name,
                         const PkgByName& pkg_by_name,
                         std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(src_pkg).second) return false;
  if (PackageDeclaresName(src_pkg, name)) return true;
  for (const auto* it : src_pkg->items) {
    if (it->kind != ModuleItemKind::kExportDecl) continue;
    const auto& ex = it->import_item;
    if (ex.package_name == "*") {
      if (WildcardExportProvidesName(src_pkg, name, pkg_by_name, visited))
        return true;
    } else if (NamedExportProvidesName(src_pkg, ex, name, pkg_by_name,
                                       visited)) {
      return true;
    }
  }
  return false;
}

void CollectPackageImports(const PackageDecl* pkg, PackageImportSet& imports) {
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const auto& imp = item->import_item;
    if (imp.is_wildcard) {
      imports.wildcard_sources.insert(imp.package_name);
    } else {
      imports.direct_imports.insert(std::string(imp.package_name) +
                                    "::" + std::string(imp.item_name));
    }
  }
}

const PackageDecl* ResolveExportSource(const ModuleItem* item,
                                       const ImportItem& ex,
                                       const PkgByName& pkg_by_name,
                                       DiagEngine& diag) {
  auto src_it = pkg_by_name.find(ex.package_name);
  if (src_it == pkg_by_name.end()) {
    diag.Error(item->loc,
               std::format("export from unknown package '{}'", ex.package_name),
               Subclause("26.6"));
    return nullptr;
  }
  std::unordered_set<const PackageDecl*> visited;
  if (!PackageProvidesName(src_it->second, ex.item_name, pkg_by_name,
                           visited)) {
    diag.Error(
        item->loc,
        std::format("'{}' is not a candidate for import from package '{}'",
                    ex.item_name, ex.package_name),
        Subclause("26.6"));
    return nullptr;
  }
  return src_it->second;
}

void CheckExportIsImported(const PackageDecl* pkg, const ModuleItem* item,
                           const ImportItem& ex,
                           const PackageImportSet& imports, DiagEngine& diag) {
  auto key = std::string(ex.package_name) + "::" + std::string(ex.item_name);
  if (imports.direct_imports.count(key) == 0 &&
      imports.wildcard_sources.count(ex.package_name) == 0) {
    diag.Error(
        item->loc,
        std::format("export '{}::{}': '{}' is not imported in package '{}'",
                    ex.package_name, ex.item_name, ex.item_name, pkg->name),
        Subclause("26.6"));
  }
}

void ValidateOnePackageExportItem(const PackageDecl* pkg,
                                  const ModuleItem* item,
                                  const PkgByName& pkg_by_name,
                                  const PackageImportSet& imports,
                                  DiagEngine& diag) {
  const auto& ex = item->import_item;

  if (ex.package_name == "*" || ex.is_wildcard) return;

  if (ResolveExportSource(item, ex, pkg_by_name, diag) == nullptr) return;

  CheckExportIsImported(pkg, item, ex, imports, diag);
}

void RecordWildcardSourcedExport(
    const ImportItem& ex, const PackageImportSet& imports,
    std::unordered_set<std::string_view>& wildcard_export_refs) {
  if (ex.package_name == "*" || ex.is_wildcard) return;
  auto key = std::string(ex.package_name) + "::" + std::string(ex.item_name);
  if (imports.wildcard_sources.count(ex.package_name) != 0 &&
      imports.direct_imports.count(key) == 0) {
    wildcard_export_refs.insert(ex.item_name);
  }
}

bool PackageItemDeclaresName(const ModuleItem* pi, std::string_view name) {
  if (pi->name == name) return true;
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
      pi->class_decl->name == name) {
    return true;
  }
  return TypeDeclaresEnumLiteral(pi->typedef_type, name) ||
         TypeDeclaresEnumLiteral(pi->data_type, name);
}

void ReportDeclarationAfterWildcardExport(
    const PackageDecl* pkg, const ModuleItem* item,
    const std::unordered_set<std::string_view>& wildcard_export_refs,
    DiagEngine& diag) {
  for (std::string_view name : wildcard_export_refs) {
    if (PackageItemDeclaresName(item, name)) {
      diag.Error(
          item->loc,
          std::format("declaration of '{}' in package '{}' follows an export "
                      "that referenced it through a wildcard package import",
                      name, pkg->name),
          Subclause("26.6"));
    }
  }
}

void CheckExportReferenceConflicts(const PackageDecl* pkg,
                                   const PackageImportSet& imports,
                                   DiagEngine& diag) {
  std::unordered_set<std::string_view> wildcard_export_refs;
  for (const auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kExportDecl) {
      RecordWildcardSourcedExport(item->import_item, imports,
                                  wildcard_export_refs);
      continue;
    }
    ReportDeclarationAfterWildcardExport(pkg, item, wildcard_export_refs, diag);
  }
}

}  // namespace

void Elaborator::ValidatePackageExports() {
  PkgByName pkg_by_name;
  for (const auto* pkg : unit_->packages) {
    pkg_by_name[pkg->name] = pkg;
  }

  for (const auto* pkg : unit_->packages) {
    PackageImportSet imports;
    CollectPackageImports(pkg, imports);

    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kExportDecl) continue;
      ValidateOnePackageExportItem(pkg, item, pkg_by_name, imports, diag_);
    }

    CheckExportReferenceConflicts(pkg, imports, diag_);
  }
}

namespace {

bool IsModportLiteralExpr(const Expr* e) {
  if (!e) return false;
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    default:
      return false;
  }
}

struct ModportNameScope {
  std::unordered_set<std::string_view> declared_names;
  std::unordered_set<std::string_view> clocking_names;
  std::unordered_set<std::string_view> constant_names;
};

void AddModportItemName(const ModuleItem* item, ModportNameScope& scope) {
  if (item->name.empty()) return;
  if (item->kind == ModuleItemKind::kClockingBlock) {
    scope.clocking_names.insert(item->name);
  }
  if (item->kind == ModuleItemKind::kParamDecl ||
      (item->kind == ModuleItemKind::kVarDecl && item->data_type.is_const)) {
    scope.constant_names.insert(item->name);
  }
  scope.declared_names.insert(item->name);
}

void CollectModportDeclaredNames(const ModuleDecl* iface,
                                 ModportNameScope& scope) {
  for (const auto& port : iface->ports) {
    if (!port.name.empty()) scope.declared_names.insert(port.name);
  }
  for (const auto& [pname, pexpr] : iface->params) {
    if (!pname.empty()) scope.constant_names.insert(pname);
  }
  for (const auto* item : iface->items) AddModportItemName(item, scope);
}

void CheckSimpleModportItemDeclared(
    const ModuleDecl* iface, const ModportDecl* mp, const ModportPort& port,
    const std::unordered_set<std::string_view>& declared_names,
    DiagEngine& diag) {
  if (!port.is_clocking && !port.is_import && !port.is_export &&
      !port.is_named_port && !declared_names.contains(port.name)) {
    diag.Error(mp->loc,
               std::format("modport '{}' references '{}', which interface '{}' "
                           "does not declare",
                           mp->name, port.name, iface->name),
               Subclause("25.5"));
  }
}

bool IsModportConstExpr(
    const Expr* e, const std::unordered_set<std::string_view>& constant_names) {
  if (IsModportLiteralExpr(e)) return true;
  if (e && e->kind == ExprKind::kIdentifier &&
      constant_names.contains(e->text)) {
    return true;
  }
  return false;
}

void CheckModportConstExprDirection(
    const ModportDecl* mp, const ModportPort& port,
    const std::unordered_set<std::string_view>& constant_names,
    DiagEngine& diag) {
  if (IsModportConstExpr(port.expr, constant_names) &&
      (port.direction == Direction::kOutput ||
       port.direction == Direction::kInout)) {
    diag.Error(mp->loc,
               std::format("port-id '{}' in modport '{}' has a constant port "
                           "expression and cannot be declared as output or "
                           "inout",
                           port.name, mp->name),
               Subclause("25.5.4"));
  }
}

void CheckModportClockingDeclared(
    const ModuleDecl* iface, const ModportDecl* mp, const ModportPort& port,
    const std::unordered_set<std::string_view>& clocking_names,
    DiagEngine& diag) {
  if (port.is_clocking && !clocking_names.contains(port.name)) {
    diag.Error(mp->loc,
               std::format("clocking identifier '{}' in modport '{}' is not "
                           "declared in interface '{}'",
                           port.name, mp->name, iface->name),
               Subclause("25.5.5"));
  }
}

void ValidateOneModportPort(const ModuleDecl* iface, const ModportDecl* mp,
                            const ModportPort& port,
                            const ModportNameScope& scope, DiagEngine& diag) {
  CheckSimpleModportItemDeclared(iface, mp, port, scope.declared_names, diag);
  CheckModportConstExprDirection(mp, port, scope.constant_names, diag);
  CheckModportClockingDeclared(iface, mp, port, scope.clocking_names, diag);
  CheckModportImport(iface, mp, port, diag);
}

void ValidateOneModport(const ModuleDecl* iface, const ModportDecl* mp,
                        const ModportNameScope& scope, DiagEngine& diag) {
  std::unordered_set<std::string_view> port_names;
  for (const auto& port : mp->ports) {
    if (port.name.empty()) continue;
    if (!port_names.insert(port.name).second) {
      diag.Error(mp->loc,
                 std::format("duplicate port-id '{}' in modport '{}'",
                             port.name, mp->name),
                 Subclause("25.5.4"));
    }
    ValidateOneModportPort(iface, mp, port, scope, diag);
  }
}

void ValidateModportsOf(const ModuleDecl* decl, DiagEngine& diag) {
  if (decl->decl_kind == ModuleDeclKind::kInterface) {
    ModportNameScope scope;
    CollectModportDeclaredNames(decl, scope);
    for (auto* mp : decl->modports) ValidateOneModport(decl, mp, scope, diag);
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl != nullptr)
      ValidateModportsOf(item->nested_module_decl, diag);
  }
}

}  // namespace

void Elaborator::ValidateModports() {
  for (const auto* decls :
       {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
    for (const auto* decl : *decls) ValidateModportsOf(decl, diag_);
  }
}

}  // namespace delta
