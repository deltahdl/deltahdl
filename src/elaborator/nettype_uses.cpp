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

// The nettypes a scope names bare, and those it names through a package or
// `$unit`, under their NamedTypeKey keys.
struct NettypeScan {
  const std::unordered_set<std::string_view>& nettypes;
  const std::unordered_set<std::string_view>& scoped;
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

// A name written behind a scope is that scope's type, and no nettype of this
// module or compilation unit, whatever its spelling: a package's or the unit's
// nettype under its "P::nt" key, and nothing behind a class, which declares no
// nettype.
static bool NamesNettype(DataTypeKind kind, std::string_view scope,
                         std::string_view name, const NettypeScan& scan) {
  if (kind != DataTypeKind::kNamed) return false;
  if (scope.empty()) return scan.nettypes.count(name) != 0;
  return scan.scoped.count(NamedTypeKey(scope, name)) != 0;
}

static bool IsNettype(const DataType& dtype, const NettypeScan& scan) {
  return NamesNettype(dtype.kind, dtype.scope_name, dtype.type_name, scan);
}

// The members of a structure or union, and of every one written in place
// inside it.
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

// The nettype a cast's casting_type names, by the name it is written with, or
// an empty string when it names none. The parser keeps a bare type name as the
// cast's text and a name written through a package as its type expression, the
// scope resolution `P::nt`.
static std::string CastNettype(const Expr& cast, const NettypeScan& scan) {
  if (scan.nettypes.count(cast.text) != 0) return std::string(cast.text);
  const Expr* type = cast.rhs;
  if (type == nullptr || type->kind != ExprKind::kMemberAccess ||
      !type->is_scope_resolution || type->lhs->kind != ExprKind::kIdentifier)
    return {};
  std::string key = NamedTypeKey(type->lhs->text, type->rhs->text);
  return scan.scoped.count(key) != 0 ? key : std::string();
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

// A procedural block declares variables alone, so a nettype naming the type
// of one of its declarations is never a net's.
static void CheckStmt(const Stmt* s, const NettypeScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl && IsNettype(s->var_decl_type, scan)) {
    ReportNettypeNotNet(NamedTypeKey(s->var_decl_type),
                        std::format("variable '{}'", s->var_name),
                        s->range.start, scan.diag);
  }
  ForEachChildExpr(s, [&scan](const Expr* e) { CheckExpr(e, scan); });
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { CheckStmt(sub, scan); });
}

// A function's return and a subroutine's arguments.
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
  for (const Stmt* s : item->func_body_stmts) CheckStmt(s, scan);
}

static void CheckClass(const ClassDecl* cls, const NettypeScan& scan);

static void CheckItem(const ModuleItem* item, const NettypeScan& scan) {
  if (item->class_decl != nullptr) CheckClass(item->class_decl, scan);
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

// A class property is a variable (§8.3), and a method, a typedef and a class
// nested in the class are judged as the module's own would be.
static void CheckClass(const ClassDecl* cls, const NettypeScan& scan) {
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

void CheckNettypeUses(const ModuleDecl* decl,
                      const std::unordered_set<std::string_view>& nettypes,
                      DiagEngine& diag) {
  if (nettypes.empty()) return;
  const NettypeScan kScan{nettypes, nettypes, diag};
  for (const ModuleItem* item : decl->items) CheckItem(item, kScan);
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

// The nettypes `items` declare.
static std::unordered_set<std::string_view> DeclaredNettypes(
    const std::vector<ModuleItem*>& items) {
  std::unordered_set<std::string_view> names;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kNettypeDecl) names.insert(item->name);
  }
  return names;
}

// A package's or the compilation unit's items, among which a variable
// declared with a nettype is judged here, no module's elaboration reaching it.
static void CheckScopeItems(const std::vector<ModuleItem*>& items,
                            const NettypeScan& scan) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        WrittenAsDataDeclaration(item) && IsNettype(item->data_type, scan)) {
      ReportNettypeNotNet(NamedTypeKey(item->data_type),
                          std::format("variable '{}'", item->name), item->loc,
                          scan.diag);
    }
    CheckItem(item, scan);
  }
}

// §26.2 (printed page 807): a package holds no process, so a net it declares
// carries no implicit continuous assignment, a net of a user-defined nettype
// (§6.6.7) as much as one of a built-in net type. The parser makes the first a
// variable declaration, which ValidatePackageItems does not ask of a net's
// initializer, so it is asked here, where the package's nettypes are known.
static void ReportPackageNettypeNetInits(const std::vector<ModuleItem*>& items,
                                         const NettypeScan& scan) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        !WrittenAsDataDeclaration(item) && item->init_expr != nullptr &&
        IsNettype(item->data_type, scan)) {
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
  const NettypeScan kUnitScan{kUnitNettypes, scoped, diag};
  CheckScopeItems(unit->cu_items, kUnitScan);
  for (const ClassDecl* cls : unit->classes) CheckClass(cls, kUnitScan);
  for (const PackageDecl* pkg : unit->packages) {
    const std::unordered_set<std::string_view> kPackageNettypes =
        DeclaredNettypes(pkg->items);
    const NettypeScan kPackageScan{kPackageNettypes, scoped, diag};
    CheckScopeItems(pkg->items, kPackageScan);
    ReportPackageNettypeNetInits(pkg->items, kPackageScan);
  }
}

}  // namespace delta
