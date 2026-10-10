#include "elaborator/nettype_uses.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct NettypeScan {
  const std::unordered_set<std::string_view>& nettypes;
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

// A name written behind a package or class scope is that scope's type, and
// no nettype of this module or compilation unit, whatever its spelling.
static bool NamesNettype(DataTypeKind kind, std::string_view scope,
                         std::string_view name, const NettypeScan& scan) {
  return kind == DataTypeKind::kNamed && scope.empty() &&
         scan.nettypes.count(name) != 0;
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
      ReportNettypeNotNet(m.type_name, std::format("member '{}'", m.name), loc,
                          scan.diag);
    }
    if (m.nested_type != nullptr) CheckMembers(*m.nested_type, loc, scan);
  }
}

static void CheckExpr(const Expr* e, const NettypeScan& scan) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCast && scan.nettypes.count(e->text) != 0) {
    ReportNettypeNotNet(e->text, "a cast", e->range.start, scan.diag);
  }
  ForEachExprChild(e, [&scan](const Expr* child) { CheckExpr(child, scan); });
}

// A procedural block declares variables alone, so a nettype naming the type
// of one of its declarations is never a net's.
static void CheckStmt(const Stmt* s, const NettypeScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl && IsNettype(s->var_decl_type, scan)) {
    ReportNettypeNotNet(s->var_decl_type.type_name,
                        std::format("variable '{}'", s->var_name),
                        s->range.start, scan.diag);
  }
  ForEachChildExpr(s, [&scan](const Expr* e) { CheckExpr(e, scan); });
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { CheckStmt(sub, scan); });
}

// A function's return and a subroutine's arguments.
static void CheckSubroutine(const ModuleItem* item, const NettypeScan& scan) {
  if (IsNettype(item->return_type, scan)) {
    ReportNettypeNotNet(item->return_type.type_name,
                        std::format("the return of function '{}'", item->name),
                        item->loc, scan.diag);
  }
  for (const FunctionArg& arg : item->func_args) {
    if (IsNettype(arg.data_type, scan)) {
      ReportNettypeNotNet(
          arg.data_type.type_name,
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
    ReportNettypeNotNet(item->data_type.type_name,
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
      ReportNettypeNotNet(m->data_type.type_name,
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
  const NettypeScan kScan{nettypes, diag};
  for (const ModuleItem* item : decl->items) CheckItem(item, kScan);
  for (size_t i = 0; i < decl->param_types.size(); ++i) {
    if (IsNettype(decl->param_types[i], kScan)) {
      ReportNettypeNotNet(decl->param_types[i].type_name,
                          std::format("parameter '{}'", decl->params[i].first),
                          decl->range.start, diag);
    }
  }
}

}  // namespace delta
