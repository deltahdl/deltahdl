#include "elaborator/nettype_uses.h"

#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct NettypeScan {
  const std::unordered_set<std::string_view>& nettypes;
  const std::unordered_set<std::string_view>& scoped;
  const std::unordered_set<std::string>& class_scoped;
  DiagEngine& diag;
};

}  // namespace

void ReportNettypeNotNet(std::string_view nettype, std::string_view use,
                         SourceLoc loc, DiagEngine& diag) {
  diag.Error(loc,
             std::format("nettype '{}' may declare only a net, and is named "
                         "here as the type of {}",
                         nettype, use),
             Subclause("6.6.7"));
}

static bool IsScopedNettypeKey(const std::string& key,
                               const NettypeScan& scan) {
  return scan.scoped.count(key) != 0 || scan.class_scoped.count(key) != 0;
}

static bool NamesNettype(DataTypeKind kind, std::string_view scope,
                         std::string_view name, const NettypeScan& scan) {
  if (kind != DataTypeKind::kNamed) return false;
  if (scope.empty()) return scan.nettypes.count(name) != 0;
  return IsScopedNettypeKey(NamedTypeKey(scope, name), scan);
}

static bool IsNettype(const DataType& dtype, const NettypeScan& scan) {
  return NamesNettype(dtype.kind, dtype.scope_name, dtype.type_name, scan);
}

static void CheckMembers(const DataType& dtype, SourceLoc loc,
                         const NettypeScan& scan) {
  for (const StructMember& m : dtype.struct_members) {
    if (NamesNettype(m.type_kind, m.scope_name, m.type_name, scan)) {
      ReportNettypeNotNet(NamedTypeKey(m.scope_name, m.type_name),
                          std::format("member '{}'", m.name), loc, scan.diag);
    }
    if (m.nested_type != nullptr) CheckMembers(*m.nested_type, loc, scan);
  }
}

static std::string CastNettype(const Expr& cast, const NettypeScan& scan) {
  if (scan.nettypes.count(cast.text) != 0) return std::string(cast.text);
  const Expr* type = cast.rhs;
  if (type == nullptr || type->kind != ExprKind::kMemberAccess ||
      !type->is_scope_resolution || type->lhs->kind != ExprKind::kIdentifier)
    return {};
  std::string key = NamedTypeKey(type->lhs->text, type->rhs->text);
  return IsScopedNettypeKey(key, scan) ? key : std::string();
}

static void CheckExpr(const Expr* e, const NettypeScan& scan) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCast) {
    const std::string kNettype = CastNettype(*e, scan);
    if (!kNettype.empty())
      ReportNettypeNotNet(kNettype, "a cast", e->range.start, scan.diag);
  }
  ForEachExprChild(e, [&scan](const Expr* child) { CheckExpr(child, scan); });
}

static void AddBodyNettypes(const std::vector<Stmt*>& body,
                            std::unordered_set<std::string_view>& names) {
  for (const Stmt* s : body) {
    if (s != nullptr && s->kind == StmtKind::kBlockItemDecl &&
        s->decl_item->kind == ModuleItemKind::kNettypeDecl)
      names.insert(s->decl_item->name);
  }
}

static NettypeScan WithLocalNettypes(
    const NettypeScan& outer, std::unordered_set<std::string_view>& local) {
  if (local.empty()) return outer;
  local.insert(outer.nettypes.begin(), outer.nettypes.end());
  return {local, outer.scoped, outer.class_scoped, outer.diag};
}

static void CheckStmt(const Stmt* s, const NettypeScan& outer) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl && IsNettype(s->var_decl_type, outer)) {
    ReportNettypeNotNet(NamedTypeKey(s->var_decl_type),
                        std::format("variable '{}'", s->var_name),
                        s->range.start, outer.diag);
  }
  ForEachChildExpr(s, [&outer](const Expr* e) { CheckExpr(e, outer); });
  std::unordered_set<std::string_view> local;
  AddBodyNettypes(s->stmts, local);
  AddBodyNettypes(s->fork_stmts, local);
  const NettypeScan kScan = WithLocalNettypes(outer, local);
  ForEachChildStmt(s, [&kScan](Stmt* const& sub) { CheckStmt(sub, kScan); });
}

static void CheckSubroutine(const ModuleItem* item, const NettypeScan& scan) {
  if (IsNettype(item->return_type, scan)) {
    ReportNettypeNotNet(NamedTypeKey(item->return_type),
                        std::format("the return of function '{}'", item->name),
                        item->loc, scan.diag);
  }
  for (const FunctionArg& arg : item->func_args) {
    if (IsNettype(arg.data_type, scan)) {
      ReportNettypeNotNet(
          NamedTypeKey(arg.data_type),
          std::format("argument '{}' of '{}'", arg.name, item->name), item->loc,
          scan.diag);
    }
  }
  std::unordered_set<std::string_view> local;
  AddBodyNettypes(item->func_body_stmts, local);
  const NettypeScan kBodyScan = WithLocalNettypes(scan, local);
  for (const Stmt* s : item->func_body_stmts) CheckStmt(s, kBodyScan);
}

static void ReportPackedDimAfterNettype(const DataType& dtype,
                                        const char* production,
                                        const NettypeScan& scan) {
  if (dtype.packed_dim_left == nullptr || !IsNettype(dtype, scan)) return;
  scan.diag.Error(dtype.packed_dim_left->range.start,
                  std::format("a net of nettype '{}' takes the nettype's data "
                              "type, and no packed dimension follows its name",
                              NamedTypeKey(dtype)),
                  Subclause(production));
}

static void CheckClass(const ClassDecl* cls, const NettypeScan& scan);

static bool DeclaresNettype(const ClassMember* m) {
  return m->kind == ClassMemberKind::kTypedef &&
         m->typedef_item->kind == ModuleItemKind::kNettypeDecl;
}

static void AddClassScopedNettypes(const ClassDecl* cls,
                                   std::unordered_set<std::string>& keys) {
  for (const ClassMember* m : cls->members) {
    if (DeclaresNettype(m)) keys.insert(NamedTypeKey(cls->name, m->name));
    if (m->nested_class != nullptr)
      AddClassScopedNettypes(m->nested_class, keys);
  }
}

static void AddItemClassScopedNettypes(const std::vector<ModuleItem*>& items,
                                       std::unordered_set<std::string>& keys) {
  for (const ModuleItem* item : items) {
    if (item->class_decl != nullptr)
      AddClassScopedNettypes(item->class_decl, keys);
  }
}

static std::unordered_set<std::string> UnitClassScopedNettypes(
    const CompilationUnit& unit) {
  std::unordered_set<std::string> keys;
  for (const ClassDecl* cls : unit.classes) AddClassScopedNettypes(cls, keys);
  for (const PackageDecl* pkg : unit.packages)
    AddItemClassScopedNettypes(pkg->items, keys);
  return keys;
}

static bool NamesClassNettype(const DataType& dtype, const NettypeScan& scan) {
  return scan.class_scoped.count(NamedTypeKey(dtype)) != 0;
}

static void ReportNettypeVariableItem(const ModuleItem* item,
                                      const NettypeScan& scan) {
  ReportNettypeNotNet(NamedTypeKey(item->data_type),
                      std::format("variable '{}'", item->name), item->loc,
                      scan.diag);
}

static void CheckItem(const ModuleItem* item, const NettypeScan& scan) {
  if (item->class_decl != nullptr) CheckClass(item->class_decl, scan);
  ReportPackedDimAfterNettype(item->data_type, "A.2.1.3", scan);
  CheckMembers(item->data_type, item->loc, scan);
  CheckMembers(item->typedef_type, item->loc, scan);
  if (item->kind == ModuleItemKind::kParamDecl &&
      IsNettype(item->data_type, scan)) {
    ReportNettypeNotNet(NamedTypeKey(item->data_type),
                        std::format("parameter '{}'", item->name), item->loc,
                        scan.diag);
  }
  CheckSubroutine(item, scan);
  CheckExpr(item->init_expr, scan);
  CheckExpr(item->assign_lhs, scan);
  CheckExpr(item->assign_rhs, scan);
  CheckStmt(item->body, scan);
}

static void CheckClass(const ClassDecl* cls, const NettypeScan& outer) {
  std::unordered_set<std::string_view> local;
  for (const ClassMember* m : cls->members) {
    if (DeclaresNettype(m)) local.insert(m->name);
  }
  NettypeScan scan = WithLocalNettypes(outer, local);
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty &&
        IsNettype(m->data_type, scan)) {
      ReportNettypeNotNet(NamedTypeKey(m->data_type),
                          std::format("property '{}'", m->name), m->loc,
                          scan.diag);
    }
    if (m->method != nullptr) CheckItem(m->method, scan);
    if (m->typedef_item != nullptr) CheckItem(m->typedef_item, scan);
    if (m->nested_class != nullptr) CheckClass(m->nested_class, scan);
  }
}

void CheckNettypeUses(const ModuleDecl* decl, const CompilationUnit& unit,
                      const std::unordered_set<std::string_view>& nettypes,
                      DiagEngine& diag) {
  std::unordered_set<std::string> class_keys = UnitClassScopedNettypes(unit);
  AddItemClassScopedNettypes(decl->items, class_keys);
  const NettypeScan kScan{nettypes, nettypes, class_keys, diag};
  for (const PortDecl& port : decl->ports) {
    ReportPackedDimAfterNettype(port.data_type, "A.2.2.1", kScan);
  }
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        NamesClassNettype(item->data_type, kScan))
      ReportNettypeVariableItem(item, kScan);
    CheckItem(item, kScan);
  }
  for (size_t i = 0; i < decl->param_types.size(); ++i) {
    if (IsNettype(decl->param_types[i], kScan)) {
      ReportNettypeNotNet(NamedTypeKey(decl->param_types[i]),
                          std::format("parameter '{}'", decl->params[i].first),
                          decl->range.start, diag);
    }
  }
}

bool WrittenAsDataDeclaration(const ModuleItem* item) {
  return item->has_explicit_var || item->is_static || item->data_type.is_const;
}

static std::unordered_set<std::string_view> DeclaredNettypes(
    const std::vector<ModuleItem*>& items) {
  std::unordered_set<std::string_view> names;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kNettypeDecl) names.insert(item->name);
  }
  return names;
}

static void CheckScopeItems(const std::vector<ModuleItem*>& items,
                            const NettypeScan& scan) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        IsNettype(item->data_type, scan) &&
        (WrittenAsDataDeclaration(item) ||
         NamesClassNettype(item->data_type, scan))) {
      ReportNettypeVariableItem(item, scan);
    }
    CheckItem(item, scan);
  }
}

static void ReportNettypeNetInits(const std::vector<ModuleItem*>& items,
                                  const NettypeScan& scan, bool in_unit) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kVarDecl ||
        WrittenAsDataDeclaration(item) || item->init_expr == nullptr ||
        !IsNettype(item->data_type, scan) ||
        NamesClassNettype(item->data_type, scan)) {
      continue;
    }
    if (in_unit) {
      scan.diag.Error(item->loc,
                      "a net declaration with an implicit continuous "
                      "assignment cannot stand in the compilation-unit scope",
                      Subclause("3.12.1"));
    } else {
      scan.diag.Error(item->loc,
                      "net declaration with implicit continuous assignment is "
                      "not allowed in a package",
                      Subclause("26.2"));
    }
  }
}

void CheckUnitNettypeUses(const CompilationUnit* unit,
                          const std::unordered_set<std::string_view>& scoped,
                          DiagEngine& diag) {
  const std::unordered_set<std::string_view> kUnitNettypes =
      DeclaredNettypes(unit->cu_items);
  const std::unordered_set<std::string> kClassKeys =
      UnitClassScopedNettypes(*unit);
  const NettypeScan kUnitScan{kUnitNettypes, scoped, kClassKeys, diag};
  CheckScopeItems(unit->cu_items, kUnitScan);
  ReportNettypeNetInits(unit->cu_items, kUnitScan, true);
  for (const ClassDecl* cls : unit->classes) CheckClass(cls, kUnitScan);
  for (const PackageDecl* pkg : unit->packages) {
    const std::unordered_set<std::string_view> kPackageNettypes =
        DeclaredNettypes(pkg->items);
    const NettypeScan kPackageScan{kPackageNettypes, scoped, kClassKeys, diag};
    CheckScopeItems(pkg->items, kPackageScan);
    ReportNettypeNetInits(pkg->items, kPackageScan, false);
  }
}

}  // namespace delta
